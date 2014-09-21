(*This is a remote controller for a map reduce function*)

open Async.Std
open Protocol
open MapReduce


let q : 'a AQueue.t ref = ref (AQueue.create ())

let addresses : 'a list ref = ref []

let num_workers : int ref = ref 0


exception InfrastructureFailure of string 
exception MapFailed of string
exception ReduceFailed of string


let init addrs = (print_endline "entering init" ); List.fold_right (fun elem acc -> (addresses := elem :: !addresses)) addrs ()


let rec add_key requests (key,inter) = match requests with
  |[] -> (key,[inter])::requests
  |(k, i)::tl -> if k = key then (key, inter::i)::tl
                            else (k, i) :: (add_key tl (key,inter))
   

let rec combine requests mapresult = match mapresult with
   |[] -> requests
   | (key,inter)::tl -> requests >>= (fun r -> combine 
                                              (return (add_key r (key,inter)) ) 
                                               tl 
                                      )  

(* let combine list mapresult = let f (key,inter) a = 
                                 let (lst,isin) = List.fold_right 
                                      (fun elem (acc,seen) -> match elem with
                                          |(key, i ) -> ((key, inter :: i) 
                                                          :: acc,seen+  1)
                                          |(k , i)  -> ((k, i ) :: acc, seen+0)
                                      ) a ([],0) 
                                 in (match isin with
                                   |0 -> (key, [inter]) :: lst
                                   |_ -> lst )
                              
             in List.fold_right f mapresult list   *)


                  

module Make (Job : MapReduce.Job) = 
struct

  module WReq = Protocol.WorkerRequest(Job) 
  module WRes = Protocol.WorkerResponse(Job)

  let get_srw addrs = try_with( fun () -> Tcp.connect (Tcp.to_host_and_port (fst(addrs)) (snd(addrs))))
                           >>| function
                                 | Core.Std.Ok(srw) ->  ((num_workers := !num_workers + 1);
                                                         (match srw with
                                                          |(s,r,w) -> (Writer.write_line w (Job.name)));
                                                        (Some (return srw) ) )
                                 | Core.Std.Error(exp) -> None

  let connect addrs = don't_wait_for (List.fold_right (fun elem acc -> (get_srw elem) >>| (fun srw -> 
                                                match srw with
                                                  |Some x -> (print_endline "connected to a worker");
                                                             AQueue.push !q x;
                                                  |None ->  (); )
                                                  ) addrs (return ())
                                )

  let rec close_workers () = if (!num_workers <> 0 ) then ((AQueue.pop !q) >>= (fun srw -> srw >>= 
                                                                                 ( fun srw -> match srw with 
                                                                                      |(s,r,w) -> (print_endline "a worker was closed");
                                                                                                   (Socket.shutdown s `Both);
                                                                                                  
                                                                                          (num_workers := !num_workers - 1);
                                                                                          (close_workers ());
                                                                                 )
                                                                               ))
                            else ((return ());) 


  let check_map_type  s srw result = result >>= fun res -> match res with 
                                                      | `Ok(WRes.MapResult(n)) -> ((print_endline "succesful map result");
                                                                                  (AQueue.push !q srw); 
                                                                                  (return true) )
                                                      |`Ok(WRes.JobFailed((n: string))) -> (raise (MapFailed(n)) );
                                                      | `Eof -> (print_endline "WRONG RESULT TYPE");
                                                                                     (return false)
                                                      |_ -> (Socket.shutdown s `Both);
                                                             (num_workers := !num_workers - 1);
                                                             (print_endline "failed");
                                                            (if !num_workers = 0 then (raise (InfrastructureFailure("all Workers dead on map")))
                                                              else () );
                                                           (return false)

let check_reduce_type  s srw result = result >>= fun res -> match res with 
                                                      | `Ok(WRes.ReduceResult(n)) -> (print_endline "succesful reduce result");
                                                                                  (AQueue.push !q srw); 
                                                                                  (return true)
                                                      | `Ok(WRes.JobFailed(n: string)) -> (raise (ReduceFailed(n))) ;
                                                      |_ -> (Socket.shutdown s `Both);
                                                            (print_endline "failed reduce");

                                                             (num_workers := !num_workers - 1);
                                                            (if !num_workers = 0 then (raise (InfrastructureFailure("all Workers dead on reduce")))
                                                              else () );
                                                           (return false)
                                                                       

let rec helper_map elem =  AQueue.pop !q >>= 
                    (fun srwd -> srwd >>= fun srw -> ( match srw with
                                  |(s,r,w) -> ( (WReq.send w (WReq.MapRequest(elem))); 
                                              let result = (WRes.receive r) in 
                                              (check_map_type s srwd result) >>= (fun tf -> if tf then result
                                                                                    else helper_map elem)

                                            )
                                )
                                
                  )

let rec helper_reduce (key, inter) = AQueue.pop !q >>= 
                    (fun srwd -> srwd >>= fun srw -> ( match srw with
                                  |(s,r,w) -> ( (WReq.send w (WReq.ReduceRequest(key,inter))); 
                                              let result = (WRes.receive r) in 
                                              (check_reduce_type s srwd result) >>= (fun tf -> if tf then result
                                                                                    else helper_reduce (key,inter))

                                            )
                                )
                                
                  )
  
  let map_reduce inputs = 
    (connect !addresses);
    (print_endline "connected" );
    let map_phase = (List.fold_right (fun elem acc ->  (helper_map elem) :: acc
                  ) inputs [] ) in
    let maps = List.fold_right (fun elem acc -> ( elem >>= (fun mapresult ->
                                (match mapresult with
                                  |`Ok(m) -> (match m with
                                    |WRes.MapResult(n) -> (print_endline "hello there");
                                                          (combine acc n )
                                    |_ -> failwith "was not a mapresult")
                                  |`Eof -> failwith "Job Failed"
                                )
                                   
                                 )) ) 
                                    map_phase (return [])
               
     in let reducesend = maps >>= (fun m -> return 
         (List.fold_right (fun (key,lis) acc -> (key, (helper_reduce (key,lis) )) ::acc) m []) 
                                  )

      in let final_list = (reducesend >>= fun rdsnd -> List.fold_right (fun (key,output) acc -> acc >>= fun a -> output >>= fun o -> match o with
                                                            |`Ok(result)-> (match result with
                                                                        |WRes.ReduceResult(job_out) -> (print_endline "hi" ); return ((key,job_out) :: a)
                                                                        |_ -> failwith "not a reduce result"
                                                                            )
                                                            |_ -> failwith "not a result"
                                                          ) rdsnd (return [])
                          )

    in don't_wait_for(close_workers ());
      (print_endline "closed workers" );
        
        final_list
                                              
          


end

