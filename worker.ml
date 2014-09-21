(*This is a worker that runs with the remote controller, also in this project folder*)

open Async.Std

module Make (Job : MapReduce.Job) = struct

  module WReq = Protocol.WorkerRequest(Job) 
  module WRes = Protocol.WorkerResponse(Job)
  
  (* see .mli *)
  
  let map_helper input w = (try_with(fun () -> Job.map input) >>| 
  function 
    |Core.Std.Ok(kilist) -> (WRes.send w (WRes.MapResult(kilist)));
    |Core.Std.Error(exp) -> (WRes.send w (WRes.JobFailed(Core.Exn.to_string exp)));
  )

  let reduce_helper input w = (try_with (fun () -> Job.reduce input) >>| 
  function 
    |Core.Std.Ok(output) -> (WRes.send w (WRes.ReduceResult(output)));
    |Core.Std.Error(exp) -> (WRes.send w (WRes.JobFailed(Core.Exn.to_string exp)));
)

  let run r w = 
  (WReq.receive r) >>= (fun request -> (match request with
                                        |`Ok(WReq.MapRequest(input))-> (map_helper input w);
                                        |`Ok(WReq.ReduceRequest(key,interlist)) -> (reduce_helper (key,interlist) w);              
                                        |`Eof -> failwith "End of file error"
                                       )
                       )


end

(* see .mli *)
let init port =
  Tcp.Server.create
    ~on_handler_error:`Raise
    (Tcp.on_port port)
    (fun _ r w ->
      Reader.read_line r >>= function
        | `Eof    -> return ()
        | `Ok job -> match MapReduce.get_job job with
          | None -> return ()
          | Some j ->
            let module Job = (val j) in
            let module Mapper = Make(Job) in
            Mapper.run r w
    )
    >>= fun _ ->
  print_endline "server started";
  print_endline "worker started.";
  print_endline "registered jobs:";
  List.iter print_endline (MapReduce.list_jobs ());
  never ()


