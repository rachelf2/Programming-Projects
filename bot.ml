(*This is a bot that plays Settlers of Caran*)

(* General Strategy:
* chose initial move by finding best hex based of separation of hexes, likelihood of roll, and predetermined "usefullness" of resource.
* discardrequest: chose resources that we dont need to build our goal 
* robbermove: calculate (excluding hexes that we touch) which hex generates most resources for oppenents. chooses color that has most of what were looking for.
* accept a trade if they are asking for something that we have a lot of, and we can spare (based on what our current build goal is)
* send out a trade request if someone has our most needed resource and we can spare something
* cards:
play knight if robber is on a hex we touch or we have a lot of them
play monopoly if we are one resource type short of building our goal and there is enough of that resource out there to get us to our goal
play year of plenty if we are 2 resources away from building our goal
play roadbuilding immediately

GENERALLY: 
play knight and get our resources below 7 before rolling (by buying or building things) 
after roll:
try to build things in this order: our current goal , city , town, road, card
change goal to city after we have 4 towns or if we cant expand roads anymore
*)



open Definition
open Registry
open Constant
open Util
open Print

(********************************************************************************************************************************)
type portg = {line: line; ratio: ratio; portresource: portresource}
type handg = {inventory: inventory; cards: cards}
type structuresg = {intersection_list: intersection list; road_list: road list}
type mapg = {hex_list: hex list; port: portg list}
type playerg = {color: color; hand: handg; trophies: trophies}
type nextg = {color: color; request: request}
type boardg = {map: mapg; structures: structuresg; deck: deck; discard: card list; robber: piece}
type game = {board: boardg; playerlist: playerg list; turn: turn; next: nextg}
type goal = Road | Town | City
type my_place = { settlement : settlement ; point : point ; hex_list : (piece * hex) list }

let (current_goal : goal ref) = ref Town

let (my_places : my_place list ref) = ref []

let (previous_trades : trade list ref) = ref [] 

let print_my_places (myplaces : my_place list ref) : unit = 
print ( String.concat "" ["my places: " ; 
  string_of_list ( fun my_place -> String.concat "" ["settlement: " ; string_of_settlement my_place.settlement 
                                                  ; ", point: " ; string_of_int my_place.point
                                                  ; ", hexs: " ; string_of_list (fun (p,h) -> 
                                                                                  String.concat "" ["(" ; string_of_int p ; "," ; string_of_terrain (fst(h)) ; ")"] ) my_place.hex_list
                                                  ]
                )  !myplaces
]) 

let print_goal () : unit = match !current_goal with
  |Road -> print "current goal: Road"
  |Town -> print "current goal: Town"
  |City -> print "current goal: City"

let game_of_state (s : state)  = 
  let structnew =
  match s with
    |(b,pl,t,n) -> match b with 
          |(map,structures,deck,discard,robber) -> match structures with
                              |(intlst,rdlst)-> {intersection_list= intlst; road_list=rdlst} in
  let playernew= 
  match s with 
    |(b,pl,t,n) -> (List.fold_right (fun ele acc-> match ele with
                          |(color,(inventory,cards),trophies) -> 
                          {color = color; hand = {inventory = inventory; cards= cards}; trophies = trophies}::acc 
                    ) pl []) in
  let mapnew = match s with
    |(b,pl,t,n) -> match b with
          |(map,str,dec,dis,rob)-> match map with
            |(hexlst, prtlist) -> 
            let newprtlist= List.fold_right (fun ele acc -> match ele with
                            |(l,r,pr) -> {line = l; ratio = r; portresource = pr}::acc ) prtlist [] in
            {hex_list = hexlst; port = newprtlist} in 


  let nextnew = match s with
    |(b,pl,t,n) -> match n with 
          |(color,request) -> {color = color; request = request} in
  let boardnew = match s with
    |(b,pl,t,n) -> match b with 
        |(map, struc, deck, disc, robber)-> {map = mapnew; structures = structnew; deck = deck; discard = disc; robber = robber}
      in

  let turn = match s with
    |(b,pl,t,n) -> t in 


  {board = boardnew; playerlist = playernew; turn = turn; next = nextnew}
(*****************************************************************************************************************************************)



(*****************************************************************************************************************************************)
(**HELPER FUNCTIONS**)
(*****************************************************************************************************************************************)



let create_my_place (settlement : settlement) (point : point) (map : mapg) : my_place = 
  let hexlst  = (List.map (fun (piece : piece) -> (piece , (List.nth (map.hex_list) piece) )) (adjacent_pieces point)) in 

  { settlement = settlement ; point = point ; hex_list = hexlst}

let update_settlements (g:game) (my_places : my_place list ref) (my_color : color) : unit = 
  let rec update (intlst : intersection list) (index : int) : my_place list= (match intlst with
    |[] -> []
    |h :: tl -> (match h with
      |None -> update tl (index + 1)
      |Some (c,tc) -> if c = my_color then (create_my_place tc index g.board.map) :: (update tl (index + 1))
                      else update tl (index + 1) ) )
  in let temp_list = update g.board.structures.intersection_list 0 in 
  (my_places := temp_list); ()

let cost_of_goal () : cost = match !current_goal with
  |Town -> cCOST_TOWN
  |City -> cCOST_CITY
  |Road -> cCOST_ROAD

(*Finds the player in playerlist given a color*)
let rec find_player (color : color) (lis : playerg list) : playerg = 
             let playeropt = List.fold_right (fun (ele:playerg) acc -> if ele.color = color then Some ele else acc) lis None in
                get_some playeropt

(*Finds all points that the given color has a road on*)
let find_current_points (rdlst : road list) (col : color) : point list = List.fold_right (fun ele acc -> match ele with 
                                                          |(color,(p1,p2)) -> if color = col then (p1::p2::acc) else acc )
                                                    rdlst []

(*Finds all already build roads*)
let find_all_roads (rdlst : road list) : line list = List.fold_right (fun ele acc -> match ele with 
                                                          |(_,line) -> line::acc ) rdlst []

(*Finds a possible road in which you can build given a point to build from and a road list*)
let rec find_new_road points allroads = match points with 
                        |[]-> None
                        |p::t -> let adjacent = adjacent_points p in 
                                let possible = List.fold_right (fun ele acc -> if List.mem (p,ele) allroads || List.mem (ele,p) allroads
                                                                                then acc else ele::acc) adjacent [] in 
                                if List.length possible = 0 then find_new_road t allroads else
                                  match possible with 
                                  |[]-> None
                                  |h::t -> Some(p,h)

let rec find_possible_roads ( points : point list) (allroads : line list) (acc : (point * point list) list) : (point * point list) list  = match points with
                        |[] -> acc
                        |p::t -> let (adjacent : point list ) = adjacent_points p in 
                                  let ( possible : point list)  = List.fold_right (fun ele ac -> if List.mem (p,ele) allroads || List.mem (ele,p) allroads
                                                                                then ac else ele::ac) adjacent [] in 
                                  find_possible_roads t allroads ((p,possible)::acc) 

(*Checks requirement that a town cannot be built within two spots of an already built town*)
let rec check_settle (point : point) (intlst : Definition.intersection list) : bool = 
  List.fold_left (fun acc elem -> match (List.nth intlst elem ) with
                    | None -> acc
                    | Some s -> false ) true (point::(adjacent_points point)) 


(*Matches a roll with the probability that it will be rolled*)
let dots roll = match roll with
        |2 -> 1
        |3 -> 2
        |4 -> 3
        |5 -> 4
        |6 -> 4
        |8 -> 4
        |9 -> 4
        |10 -> 3
        |11 -> 2
        |12 -> 1
        |_ -> 1

(*Ranks terrains with use value*)
let terrainpnts ter = match ter with 
        |Hill -> 5
        |Forest -> 4
        |Mountain -> 3
        |Field -> 2
        |Pasture -> 1
        |Desert -> -1 

(*Finds desirability of an initial intersection*)
let desirability pnt board :int = let hexesindex = adjacent_pieces pnt in
                                  let hexes = List.fold_right (fun hxind acc -> 
                                                    try List.nth board.map.hex_list hxind::acc
                                                              with _ -> acc) hexesindex []
                                  in 
                                  let totaldots = List.fold_right (fun hex acc -> dots (snd(hex)) + acc) hexes 0 in 
                                  let totalterrain = List.fold_right (fun hex acc -> terrainpnts (fst(hex)) + acc ) hexes 0 in 
                                   totalterrain + totaldots

let not_through_settlement (p1,p2) color intersection_list roadlst = 
                          let mypnts = List.fold_right (fun (col,(p1,p2)) acc -> if col = color 
                                  then p1::p2::acc else acc) roadlst [] in 
                          let first_settle = List.nth intersection_list p1 in 
                          let sec_settle = List.nth intersection_list p2 in 
                          if is_none first_settle && is_none sec_settle then true 
                          else if List.mem p1 mypnts  
                              then if is_none first_settle then true
                                 else let (col,set) = get_some first_settle in 
                                 if col = color then true else false

                            else if is_none sec_settle then true
                                 else let (col,set) = get_some sec_settle in 
                                 if col = color then true else false


(*Ranks intersections based on if you can build on it and how desirable of a spot it is and returns best one*)
let rank_intersections intlst board plces =
        let mine_so_far = List.fold_right (fun plc acc -> (plc.point)::acc) plces [] in 
        let adjhexes = List.fold_right (fun pnt acc -> (adjacent_pieces pnt)@acc) mine_so_far [] in 
        let available = List.fold_right (fun ele (lst,num)-> if is_none ele then ((num::lst),num+1) else (lst,num+1)) 
                              intlst ([],cMIN_POINT_NUM) in 
        let buildable = List.fold_right (fun pnt acc -> if check_settle pnt intlst then pnt::acc else acc) (fst(available)) [] in 
        let no_hexes = List.fold_right (fun pnt acc -> 
                                              let new_hex = adjacent_pieces pnt in 
                                              if List.exists (fun x -> List.mem x new_hex) adjhexes then acc else pnt::acc) buildable []
                        in 
        let ranks = List.fold_right (fun pnt acc -> (pnt, desirability pnt board)::acc) no_hexes [] in 
        let best = List.fold_right (fun (pnt,rnk) (acpnt,acrnk) -> if rnk > acrnk then (pnt,rnk) else (acpnt,acrnk)) ranks (0,0) in
          fst(best)


(*Returns a list of (piece,rank) to rank desirability of putting a robber on that piece depending on towns/cities*)
let rec rank_hex (hxlst: piece list) (gme : game) (acc: (int*int) list) : (int * int) list = 
                            let intlst = gme.board.structures.intersection_list in 
                            
                            match hxlst with 
                            |[] -> acc
                            |hx::t ->
                                 ( let adj = piece_corners hx in
                                  let hex_score = List.fold_right (fun pnt ac -> 
                                                  let settle = try (List.nth intlst pnt) 
                                                              with _ ->  None in 
                                                  
                                                  (match settle with 
                                                  |None -> ac
                                                  |Some(_,typ) -> if typ = City then (ac + 2) else (ac + 1))
                                                              ) adj 0
                                  in 
                                  
                                  rank_hex t gme ((hx, hex_score)::acc) )

(*Folds over list of ranked pieces to determine which is best for putting robber on*)
let find_best_hex ( rnkedhexes : (int * int) list ) = List.fold_right (fun (pnt,rnk) (acpnt,acrnk) -> if rnk > acrnk then (pnt,rnk) 
                               else (acpnt,acrnk)) rnkedhexes (0,0)


(*Determines most needed resource as an option*)
let most_needed_option (me : playerg) : resource option = 
                      let inv = me.hand.inventory in 
                      let what_i_need = map_cost2 (-) (cost_of_goal ()) inv in 
                       let (what_howmuch :(resource option * int) list) = 
                        List.fold_right (fun resource acc -> let amt = num_resource_in_inventory what_i_need resource in if amt > 0 then (Some resource , amt ) :: acc else acc ) [Brick ; Wool ; Ore ; Grain ; Lumber] [] 
                      in
                      match (List.fold_right (fun (r1,i1) (r2,i2) -> if i1 > i2 then (r1,i1) else (r2,i2)) what_howmuch (None,0) ) with
                                                            |(a,_) -> a 

(* returns my most needed resource *) 
let most_needed (me : playerg) : resource = 
                       let goal = !current_goal in
                       let inv = me.hand.inventory in 
                       let (b,w,o,g,l) = inv in 
                       match goal with 
                       |Road -> if min b l = b then Brick else Lumber
                       |Town -> let least = min (min (min b w) g) l in 
                                if least = b then Brick else 
                                if least = l then Lumber else
                                if least = o then Ore else
                                 Wool
                       |City -> if min o g = o then Ore else Grain  



(*Returns a list of colors settled around a hex*)
let rec coloroptions (pntlst :int list) (intlst: (color * settlement) option list) acc= match pntlst with 
                           |[]-> acc
                           |pnt::t ->( let settle = try List.nth intlst pnt
                                                   with _ ->  None in 
                                      
                                      (match settle with 
                                       |None -> coloroptions t intlst acc
                                       |Some(col,_) -> coloroptions t intlst (col::acc) )  )

(*Gives the color that has the most of the desired resource*)
let find_best_color (clist: color list) res plist : (color option * int) = List.fold_right (fun col (bc,numres)-> 
                                              let play = find_player col plist in 
                                              let num = num_resource_in_inventory play.hand.inventory res in 
                                              if num > numres then (Some col,num) else (bc, numres)) clist (None,-1)

(*Takes in point list and a piece and returns list of pieces that the color is not settled on*)
let rec find_hexes mypoints (pice: piece) acc = if pice > cMAX_PIECE_NUM then acc
                                     else let adj = piece_corners pice in 
                                     if List.exists (fun x -> List.mem x adj) (fst(mypoints)) then find_hexes mypoints (pice + 1) acc
                                      else 
                                      find_hexes mypoints (pice + 1) (pice::acc)

(* returns how many resources i have to discard in discardRequest (floor of half of the number I have) *)
let floor_half (inventory : inventory) : int = (int_of_float (floor( (/.) (float (sum_cost inventory) ) 2.0)))



(* gives a list of the resources, with a generic ranking of how often you generate it*)
let calculate_resource_availability (my_places: my_place list ref) : (resource * int) list = 
  let available_cost (my_place : my_place) = 
    let rec ac (hexlst : (piece * hex) list) (amt : int) : cost = (match hexlst with
      |[] -> (0,0,0,0,0)
      | (p,h) :: tl -> (match h with
        |(t,r) -> let res = (resource_of_terrain t) in (match res with
          |None -> ac tl amt
          |Some(re) -> map_cost2 (+) (map_cost (fun x -> (dots r) * amt * x) (single_resource_cost re)) (ac tl amt))
      )) 
    in ac my_place.hex_list (settlement_num_resources my_place.settlement)
  in
  let rec cra (mpl : my_place list) : cost = match mpl with 
    | [] -> (0,0,0,0,0)
    | h :: tl -> map_cost2 (+) (available_cost h) (cra tl)
  in match (cra !my_places) with
    |(b,w,o,g,l) -> [( Brick , b) ; (Wool , w) ; (Ore , o) ; (Grain , g) ; (Lumber, l)]

(* generate a random resource that has at least one element in inv *)
let get_random_resource (inv :inventory) : resource option = 
                            let rec f (rlst : resource list) : resource option = 
                            (match (pick_random rlst) with
                              |None -> None
                              |Some r ->  if (num_resource_in_inventory inv r) > 0 
                                          then Some r 
                                          else f (list_memremove (fun a -> a = r) rlst)) in
                            f [Brick; Wool; Ore; Grain; Lumber]



(* return the resource that you generate most often in inv, and therefore are willing to trade *)
let get_least_important_resource (inv : inventory) (myplaces : my_place list ref) : resource option = 
  let reslst = 
    List.sort (fun a b -> if (snd(a)) < (snd(b)) then -1 
    else if (snd(a)) > (snd(b)) then 1 
    else 0) (calculate_resource_availability myplaces) in 
    let rec f lst = 
                              match lst with 
                                | [] -> get_random_resource inv
                                | h :: tl -> if (num_resource_in_inventory inv (fst(h)) ) > 0 
                                            then Some (fst(h)) 
                                            else f tl 
                            in f reslst 

(* gives my least needed resource / the resource that i can spare in my inv *)
let least_needed (inv : inventory) (myplaces : my_place list ref) : resource option = 
  let got_alot =  (List.filter (fun resource -> (num_resource_in_inventory inv resource) > 3 ) [Brick;Wool;Ore;Grain;Lumber]) in
  match got_alot with
    |[] -> get_least_important_resource inv myplaces 
    | _ -> let (new_inv : inventory) = (match inv with 
                                        |(b,w,o,g,l) -> let nb = if (List.mem Brick got_alot) then b else 0 in 
                                                        let nw = if (List.mem Wool got_alot) then w else 0 in
                                                        let no = if (List.mem Ore got_alot) then o else 0 in
                                                        let ng = if (List.mem Grain got_alot) then g else 0 in
                                                        let nl = if (List.mem Lumber got_alot) then l else 0 in (nb,nw,no,ng,nl) )
            in get_least_important_resource new_inv myplaces 

let rec calculate_struct_points color (structs:Definition.intersection list) acc =  match structs with 
  |[] -> acc
  |None :: t -> calculate_struct_points color t acc
  |((Some (col,settle))::t) -> if col = color then 
    (match settle with 
    |Town -> calculate_struct_points color t (acc+cVP_TOWN)
    |City -> calculate_struct_points color t (acc + cVP_CITY)
    )
    else calculate_struct_points color t acc  

let close_to_win (g:game) :bool = let plyrlst = g.playerlist in 
                            List.fold_right (fun plyr acc -> 
                           
                            let trophypoints= 
                            match plyr.trophies with 
                            |(_,true,true)-> cVP_LONGEST_ROAD + cVP_LARGEST_ARMY
                            |(_,true,false) -> cVP_LONGEST_ROAD
                            |(_,false,true) -> cVP_LARGEST_ARMY
                            |_ -> 0
                            in

                            let structpoints =
                            calculate_struct_points plyr.color g.board.structures.intersection_list 0
                            in

                            ((if trophypoints + structpoints >= 7 then true else false) || acc)
                            
                            ) plyrlst false

(* generate list of all pieces that I have a settlement on *)
let get_my_pieces (myplacelist : my_place list) : piece list =
  List.fold_right (fun place a -> 
    (List.fold_right (fun elem ac -> match elem with 
      |(p,h) -> (if (List.mem p a) then ac else p::ac) ) place.hex_list []) @ a) myplacelist []


(* returns whether or not I should / can  play a robber card *)
let play_robber_card (g : game) (me : playerg) (myplaces : my_place list ref) : bool = let current_rob = g.board.robber in
                              let my_stuff = !myplaces in 
                              let (mypieces : piece list) = get_my_pieces my_stuff in 
                              let robber_on_me = (List.mem current_rob mypieces) in
                              let close = close_to_win g in 
                              let crds = me.hand.cards in 
                              let c = match crds with
                                      |Reveal(c) -> c 
                                      |Hidden(_) -> [] in 
                              let knight = List.mem Knight c in 
                              let numknights = List.fold_right (fun ele acc -> if ele = Knight then acc+1 else acc) c 0 in 
                              let answer = if ((close || robber_on_me) && knight) || numknights >2 then true else false in 
                              answer

(* basically, handle a robber request. returns the (piece, color option) pair to insert into a Robber Move *)
let pick_robber_move (g : game ) (me : playerg) (myplaces : my_place list) : piece * color option = let intlst = g.board.structures.intersection_list in 
                          let mypieces = get_my_pieces myplaces in 
                          let rec remove_from_hexes (pl : piece list) (index : int) (acc : piece list) = 
                            if index > cMAX_PIECE_NUM then acc else 
                            if (List.mem index pl) then remove_from_hexes pl (index + 1) acc 
                            else remove_from_hexes pl (index + 1) (index::acc) 
                          in 
                          let hexes = remove_from_hexes mypieces cMIN_PIECE_NUM [] in  
                          
                          let piece = 
                            if (List.length hexes) = 0 then (list_indexof (fun (t,_) -> t = Desert) g.board.map.hex_list)
                            else let ranked_hex = (rank_hex hexes g []) in 
                               fst(find_best_hex ranked_hex)
                          in  
                          let adjpiece = piece_corners piece in 
                          let colorops = coloroptions adjpiece intlst [] in
                          let needed = most_needed me in 
                          let best_color = (fst(find_best_color colorops needed g.playerlist)) 
                          in  
                          (piece , best_color)

let can_build_goal (me : playerg) (g : game) pref : bool = let goal = !current_goal in
                        let inv = me.hand.inventory in
                        let answer =  
                        (match goal with 
                        |Town -> let rds = g.board.structures.road_list in 
                                 let mypnts = List.fold_right (fun (col,(p1,p2)) acc-> if col = me.color 
                                              then (p1::p2::acc) else acc) rds [] in 
                                 let settled = List.fold_right (fun pnt acc -> if check_settle pnt g.board.structures.intersection_list
                                                                                then pnt::acc else acc) mypnts [] in 
                                 let can_town = if List.length settled = 0 then false else true in 
                                 if ((((num_resource_in_inventory inv Lumber > 0) &&
                                    (num_resource_in_inventory inv Brick > 0) ) &&
                                    (num_resource_in_inventory inv Grain > 0) ) &&
                                    ((num_resource_in_inventory inv Wool > 0)))
                                    && can_town then true else false
                        |City -> if ((num_resource_in_inventory inv Grain > 1) &&
                                    (num_resource_in_inventory inv Ore > 2) ) &&
                                    List.fold_right (fun ele acc -> 
                                          let settle = ele.settlement in 
                                          if settle = Town then true else false || acc) (pref) false
                                    then true else false
                        |Road -> let current_points = find_current_points g.board.structures.road_list me.color  in
                                 let all_roads = find_all_roads g.board.structures.road_list in 
                                 let newrd = find_new_road current_points all_roads in 
                                 let buildable = if newrd = None then false else true in 
                                 if (buildable && (num_resource_in_inventory inv Brick > 0) ) && 
                                 (num_resource_in_inventory inv Lumber > 0) then true else false
                        ) in answer  



let can_build_city (me : playerg) (pref : my_place list) : bool  = let inv = me.hand.inventory in 
                      
                       let own_town = 
                      (List.fold_right (fun ele acc -> 
                            let settle = ele.settlement in 
                            ((settle = Town) || acc) ) (pref) false) in 
                      
                      let answer = 
                      if (((num_resource_in_inventory inv Grain > 1) &&
                      (num_resource_in_inventory inv Ore > 2) ) && own_town)
                      then true else false 
                    
                    in answer

let can_buy_card (me : playerg) (gm : game) : bool = let inv = me.hand.inventory in 
                      let (b,w,o,g,l) = inv in 
                      let deck = gm.board.deck in 
                      let size = 
                      match deck with 
                      |Reveal(c) -> List.length c 
                      |Hidden(i) -> i 
                      in 
                      let answer = if ((w > 0 && o >0) && g > 0) && size > 0 then true else false in 

                      answer

let can_build_road (me: playerg) (g : game) : bool  =  let current_points = find_current_points g.board.structures.road_list me.color  in
                           let all_roads = find_all_roads g.board.structures.road_list in 
                           let newrd = find_new_road current_points all_roads in 
                           let buildable = if newrd = None then false else true in 
                           let answer = if buildable  then true else false in answer

(* returns whether or not we can afford to buy a road *)
let afford_road ( me : playerg) : bool = let inv = me.hand.inventory in 
                            if (num_resource_in_inventory inv Brick > 0)  && 
                           (num_resource_in_inventory inv Lumber > 0) then true else false


let can_build_town (me: playerg) (g : game) : bool  = let inv = me.hand.inventory in 
                          let rds = g.board.structures.road_list in 
                           let mypnts = List.fold_right (fun (col,(p1,p2)) acc-> if col = me.color 
                                        then (p1::p2::acc) else acc) rds [] in 
                           let settled = List.fold_right (fun pnt acc -> if check_settle pnt g.board.structures.intersection_list
                                                                          then pnt::acc else acc) mypnts [] in 
                           let can_town = if List.length settled = 0 then false else true in 
                           let answer = if ((((num_resource_in_inventory inv Lumber > 0) &&
                              (num_resource_in_inventory inv Brick > 0) ) &&
                              (num_resource_in_inventory inv Grain > 0) ) &&
                              ((num_resource_in_inventory inv Wool > 0)))
                              && can_town then true else false in answer

let best_road (rdlst : (point * (point * int)) list) : (point * (point * int)) = List.fold_right (fun (p1,(p2,r)) (ap,(ap2,ar)) -> if r > ar then (p1,(p2,r)) else (ap,(ap2,ar))) rdlst (0,(0,0))

let build_city (rpl : my_place list) : point = let pnt = List.fold_left (fun acc ele -> if ele.settlement = Town then ele.point else acc) 0 (rpl) in 
                        pnt

let build_road (g : game) (me : playerg) = 
                  let (current_points : point list) = find_current_points g.board.structures.road_list me.color  in
                  let (all_roads : line list) = find_all_roads g.board.structures.road_list in
                  let (poss : (point * point list) list) = find_possible_roads current_points all_roads [] in 
                  let (ranked_poss : (point * (point * int) list) list) = 
                  List.fold_right (fun (p1,plis) acc -> (p1,
                                                            (List.fold_right 
                                                            (fun (ele :point) ac -> (ele, desirability ele g.board)::ac) 
                                                            plis [])
                                                        )::acc) 
                                  poss [] in 
                  let best_poss = List.fold_right (fun (p1,prlis) acc -> (p1, find_best_hex prlis)::acc) ranked_poss [] in 
                  let possible_of_ranked = List.fold_right (fun (p1,(p2,r)) acc -> 
                          if not_through_settlement (p1,p2) me.color g.board.structures.intersection_list g.board.structures.road_list
                            then (p1,(p2,r))::acc else acc) best_poss [] in 
                  let (p,(p2,r)) = best_road possible_of_ranked in 
                   (p,p2)

let build_road_2 (g : game) (me : playerg) = 
                  let (current_points : point list) = find_current_points g.board.structures.road_list me.color  in
                  let (all_roads : line list) = find_all_roads g.board.structures.road_list in
                  let (poss : (point * point list) list) = find_possible_roads current_points all_roads [] in 
                  let (ranked_poss : (point * (point * int) list) list) = 
                  List.fold_right (fun (p1,plis) acc -> (p1,
                                                            (List.fold_right 
                                                            (fun (ele :point) ac -> (ele, desirability ele g.board)::ac) 
                                                            plis [])
                                                        )::acc) 
                                  poss [] in 
                  
                  let best_poss = List.fold_right (fun (p1,prlis) acc -> (p1, find_best_hex prlis)::acc) ranked_poss [] in 
                  let (p,(p2,r)) = best_road best_poss in 
                  let new_best_poss = List.fold_right (fun (one,(two,rank)) acc -> if two = p2 && one = p then acc else 
                                                    (one,(two,rank))::acc) best_poss [] in 
                  let (np,(np2,nr)) = best_road new_best_poss in 
                   (np,np2) 

let build_town ( g : game) ( me : playerg) = (* let inv = me.hand.inventory in *)
                      let rds = g.board.structures.road_list in 
                      let mypnts = List.fold_right (fun (col,(p1,p2)) acc-> if col = me.color 
                                   then (p1::p2::acc) else acc) rds [] in 
                      let settled = List.fold_right (fun pnt acc -> if check_settle pnt g.board.structures.intersection_list
                                                                    then pnt::acc else acc) mypnts [] in
                      let ranked_pnts = List.fold_right (fun pnt acc -> (pnt, desirability pnt g.board)::acc) settled [] in 
                      let best = List.fold_right (fun (pnt,rnk) (acpnt,acrnk) -> if rnk > acrnk then (pnt,rnk) else (acpnt,acrnk)) ranked_pnts (0,0) in
                        fst(best)


let can_trade (me : playerg) (g : game) : bool = 
  match most_needed_option me with
          |None -> false
          |Some r -> let i_want = r in  
  if List.exists (fun resource -> (num_resource_in_inventory me.hand.inventory resource) > 10 ) [Brick;Wool;Ore;Grain;Lumber] then true else 
  let working_inv = map_cost2 (-) me.hand.inventory (cost_of_goal ()) in
  let answer = 
  (if is_none (least_needed working_inv my_places) then false else 
  let (i_can_spare : resource) = get_some (least_needed working_inv my_places) in

  let (how_much_can_i_spare : int) = (num_resource_in_inventory working_inv i_can_spare) - (num_resource_in_inventory (cost_of_goal()) i_can_spare) in 
  if how_much_can_i_spare <= 0 then false else 
  if how_much_can_i_spare > 3  && i_can_spare <> Ore then true else 

    let ( opponents_inventories : (color * inventory) list ) = 
      List.fold_right (fun (player : playerg) acc -> if player.color = me.color || (num_resource_in_inventory player.hand.inventory i_want) = 0 then acc else (player.color , player.hand.inventory)::acc) g.playerlist [] in
    let remove_prev_trades = List.filter (fun (c,i) -> not (List.exists (fun (tc,_,c2) -> (tc = c) && (num_resource_in_inventory c2 i_want > 0) ) !previous_trades)) opponents_inventories in
    (match remove_prev_trades with
      | [] -> false 
      | _ -> true ) ) in
    answer 


(* perform a Maritime Trade when you have more then 10 of a given resource*)
let too_many_trade (inv : inventory) (i_want : resource) : action = 
  let r = List.find (fun resource -> (num_resource_in_inventory inv resource) > 10 ) [Brick;Wool;Ore;Grain;Lumber]
in MaritimeTrade(r, i_want)


(* decide which trade to do *)
let trade (g : game) (me: playerg) : action = 
  let i_want = get_some (most_needed_option me) in
  if List.exists (fun resource -> (num_resource_in_inventory me.hand.inventory resource) > 10 ) [Brick;Wool;Ore;Grain;Lumber] then too_many_trade me.hand.inventory i_want
  else 
  let working_inv = map_cost2 (-) me.hand.inventory (cost_of_goal ()) in
  let (i_can_spare : resource) = get_some (least_needed working_inv my_places) in 
    let ( opponents_inventories : (color * inventory) list ) = 
      List.fold_right (fun (player : playerg) acc -> if (player.color = me.color) || (num_resource_in_inventory player.hand.inventory i_want) = 0 then acc else (player.color , player.hand.inventory)::acc) g.playerlist [] in
    let remove_prev_trades = List.filter (fun (c,i) -> not (List.exists (fun (tc,_,c2) -> (tc = c) && (num_resource_in_inventory c2 i_want > 0) ) !previous_trades)) opponents_inventories in

    match remove_prev_trades with
      | [] -> MaritimeTrade(i_can_spare, i_want)
      | _ ->
        let (how_much_do_i_need : int) = (num_resource_in_inventory (cost_of_goal()) i_want) - (num_resource_in_inventory me.hand.inventory i_want) in
        let (how_much_can_i_spare : int) = (num_resource_in_inventory working_inv i_can_spare) - (num_resource_in_inventory (cost_of_goal()) i_can_spare) in 
        let max_amt_i_can_offer = min how_much_do_i_need how_much_can_i_spare in
        let (amts : (color * int) list) = List.map (fun (col, inv) -> (col, (min (num_resource_in_inventory inv i_want) max_amt_i_can_offer)) ) remove_prev_trades in
        let coloramt = List.fold_right (fun (c1, i1) (c2,i2) -> if i1 > i2 then (c1 , i1) else (c2 , i2)) amts (me.color,0) in
        let potential_trade = ( (fst(coloramt)) , map_cost (fun a -> a * (snd(coloramt))) (single_resource_cost i_can_spare) , map_cost (fun a -> a * (snd(coloramt))) (single_resource_cost i_want) )

      in match potential_trade with 
        |(color, c1, c2) -> if (color = me.color) || (sum_cost c1 <= 0 || sum_cost c2 <= 0) then let move = MaritimeTrade(i_can_spare, i_want) in move
                            else let move = DomesticTrade(potential_trade) in (previous_trades := potential_trade :: !previous_trades);
                                                                               move 



let count_all (res : resource) (plist : playerg list) : int  = List.fold_right (fun player acc -> 
                                                let (b,w,o,g,l) = player.hand.inventory in 
                                                match res with 
                                                |Brick -> acc + b
                                                |Wool -> acc + w
                                                |Ore -> acc + o
                                                |Grain -> acc + g
                                                |Lumber -> acc + l
                                          ) plist 0


let should_monopoly (crds : card list) (gme : game) (me : playerg) : bool = let (b,w,o,g,l) = me.hand.inventory in 

                                let diff = 
                                match most_needed me with 
                                |Brick -> if b< 2 && count_all Brick gme.playerlist >2 then true else false
                                |Wool -> if w <2 && count_all Brick gme.playerlist >2 then true else false
                                |Ore -> if o <2 && count_all Brick gme.playerlist >2 then true else false
                                |Grain -> if g <2 && count_all Brick gme.playerlist >2 then true else false
                                |Lumber -> if l <2 && count_all Brick gme.playerlist >2 then true else false
                                in 

                                if List.mem Monopoly crds && diff then true else false

let should_year_of_plenty (crds : card list) (me : playerg) : bool  = let (b,w,o,g,l) = me.hand.inventory in 
                                let goal = !current_goal in 
                                let needed = 
                                match goal with 
                                |Town -> if ((b > 0 && ((w> 0 || g> 0) || l >0)) || (w > 0 && (l> 0 || g> 0)))
                                              || (l >0 && g >0) then true else false
                                |City -> if ((o > 2 && g < 1) || (o < 2 && g >1)) || (o = 2 && g = 1) then true else false
                                |Road -> if b = 0 || l = 0 then true else false
                                in
                                if List.mem YearOfPlenty crds && needed then true else false  

let year_of_plenty (me : playerg) : resource * resource = let (b,w,o,g,l) = me.hand.inventory in 
                        let goal = !current_goal in 

                        match goal with 
                        |Road -> if b = 0 && l = 0 then (Brick,Lumber)
                                 else if b = 0 then (Brick,Brick)
                                 else (Lumber,Brick)
                        |City -> if o < 2 then (Ore, Ore)
                                 else if g < 1 then (Grain,Grain)
                                 else (Ore,Grain)
                        |Town -> if b = 1 && w = 1 then (Grain,Lumber)
                                 else if b = 1 && g = 1 then (Wool,Lumber)
                                 else if b = 1 && l = 1 then (Wool,Grain)
                                 else if w = 1 && l = 1 then (Brick,Grain)
                                 else if w = 1 && g = 1 then (Brick,Lumber)
                                 else (Brick,Wool) 


(****************************************************************************************************************************************)
(**BOT**)
(**************************************************************************************************************************************)
(** Give your bot a 2-20 character name. *)
let name = "robotBotratheon"

let (current_goal : goal ref) = ref Town

  


let (my_places : my_place list ref) = ref []

module Bot = functor (S : Soul) -> struct
  (* If you use side effects, start/reset your bot for a new game *)
   let initialize () = current_goal := Town ;
                      my_places := [] ;
                      previous_trades := [] 

  (* Invalid moves are overridden in game *)
  let handle_request ((s) : state) : move =
    let g = game_of_state s in 

    let mycolor = g.next.color in 
     (update_settlements g my_places mycolor) ;
    let me = find_player mycolor g.playerlist in
    let (c, r) = (g.next.color,g.next.request) in
    let finalchoice = 
    (match r with
      | InitialRequest -> 
                          let intlst = g.board.structures.intersection_list in 
                          let best = rank_intersections intlst g.board (!my_places) in 
                          let rdoptions = adjacent_points best in 
                          let desrds = List.fold_right (fun pnt acc -> (pnt, desirability pnt g.board)::acc) rdoptions [] in 
                          let bstrd = List.fold_right (fun (pnt,rnk) (acpnt,acrnk) -> 
                            if rnk > acrnk then (pnt,rnk) else (acpnt,acrnk)) desrds (0,0) in
                          let bestsec = fst(bstrd) in 
                            InitialMove(best, bestsec)

      | DiscardRequest->  

                          let amt_i_need_to_discard = floor_half me.hand.inventory in
                          
                          let rec generate_cost cost inv : cost = 
                            if (sum_cost cost) = amt_i_need_to_discard then cost
                            else  let potential_remaining_inv = map_cost2 (fun a b -> a - b) inv cost in 
                                  if (sum_cost potential_remaining_inv) = 0 then cost 
                                  else let resource = (least_needed potential_remaining_inv my_places) in match resource with
                                    |None -> cost 
                                    |Some c -> generate_cost (map_cost2 (+) cost (single_resource_cost c) ) inv   
                          
                          in let i_want_to_save = match !current_goal with
                            |Road -> cCOST_ROAD
                            |Town -> cCOST_TOWN
                            |City -> cCOST_CITY
                          in 
                          let remaining_inv = map_cost2 (fun a b -> if a > b then a - b else 0) me.hand.inventory i_want_to_save in
                          let potential_move = generate_cost (0,0,0,0,0) remaining_inv in
                          if (sum_cost potential_move) >= amt_i_need_to_discard then DiscardMove(potential_move)
                        else DiscardMove(generate_cost potential_move me.hand.inventory)
      
      | RobberRequest ->  RobberMove(pick_robber_move g me !my_places)
      
      | TradeRequest -> 
                        let answer = (match g.turn.pendingtrade with 
                        | None -> false
                        | Some(c,c1,c2) -> 

                        let what_i_gain = c1 in
                        let what_i_lose = c2 in

                        (* dont accept if they are asking for more than 3 resources *)
                        
                        if (sum_cost what_i_lose) > 3 then false
                        else
                        (* dont accept if they want something that we don't generate ever *)
                        
                        let resource_availability = (calculate_resource_availability my_places) in
                        let bad_offer (ralst : resource * int ) (wil : cost) : bool = (match ralst with
                          |(re, prob) -> if prob < 1 && (num_resource_in_inventory what_i_lose re) > 0 then true
                          else false ) in 
                        if (List.fold_right (fun elem acc -> (bad_offer elem what_i_lose) || acc ) resource_availability false)
                        then false 
                      else
                        let (can_we_spare : bool) = 
                          let working_inv = map_cost2 (-) me.hand.inventory (cost_of_goal()) in
                          let bool_cost = map_cost2 (fun a b -> (b = 0) || (a - b) >= 0 ) working_inv what_i_lose
                          in (match bool_cost with
                          |(b,w,o,g,l) -> b && (w && (o && (g && l))))  in 

                        if not can_we_spare then false 
                      else 
                      let (do_we_want : bool) = (
                        let what_i_need = map_cost2 (-) (cost_of_goal()) me.hand.inventory in 
                        let bool_cost = map_cost2 (fun a b -> (a > 0) && (b > 0)) what_i_gain what_i_need 
                        in (match bool_cost with
                          |(b,w,o,g,l) -> b || (w || (o || (g || l)))))  in
                        
                      if not do_we_want then false
                      else true ) in 
                    TradeResponse(answer)
      | ActionRequest -> let cards = me.hand.cards in 
                        let crds = match cards with 
                                   |Reveal(c) -> c
                                   |Hidden(_) -> [] in 
                        let goal = !current_goal in
                        
                        if (is_none g.turn.dicerolled) then 
                          ( if play_robber_card g me my_places then Action( PlayCard( PlayKnight( pick_robber_move g me !my_places) ) ) (*Wrote play robber card*)
                            else if sum_cost me.hand.inventory > 7 then 
                              if can_build_goal me g (!my_places) then (match goal with 
                                  |City -> Action( BuyBuild( BuildCity( build_city (!my_places) )))
                                  |Town -> 
                                    let move =  Action(BuyBuild(BuildTown(build_town g me))) in 
                                    (if List.length !my_places <4 then 
                                      (current_goal:= !current_goal)
                                    else (current_goal := City) ); 
                                    move
                                  |Road -> let rd = build_road g me in 
                                      Action(BuyBuild(BuildRoad((mycolor,rd)))) )
                              else if can_build_city me (!my_places) then Action(BuyBuild(BuildCity(build_city (!my_places)))) 
                              else if can_build_town me g then 
                                     let move =  Action(BuyBuild(BuildTown(build_town g me))) in 
                                    (if List.length !my_places <4 then 
                                      (current_goal:= !current_goal)
                                    else (current_goal := City) ); 
                                    move
                              else if (can_build_road me g && afford_road me) then let rd = (mycolor, build_road g me) 
                                              in Action(BuyBuild(BuildRoad(rd)))
                              else if can_buy_card me g then Action(BuyBuild(BuildCard))
                              else Action(RollDice)
                            else let move = Action(RollDice) in move
                            )
                          else
                            let rd = (mycolor, build_road g me) in 
                            let rd2 = Some (mycolor, build_road_2 g me) in 
                           if List.mem RoadBuilding crds then Action(PlayCard(PlayRoadBuilding(rd,rd2)))
                                                         else
                          (if can_build_goal me g (!my_places) then  
                            (match goal with 
                            |Town -> 
                                    let move =  Action(BuyBuild(BuildTown(build_town g me))) in 
                                    (if List.length !my_places <4 then 
                                      (current_goal:= !current_goal)
                                    else (current_goal := City) ); 
                                    (if not (can_build_road me g) then (current_goal := City)
                                    else (current_goal:= !current_goal));
                                    move
                            |City -> Action(BuyBuild(BuildCity(build_city (!my_places) )))
                            |Road -> let rd = (mycolor, build_road g me) in 
                                      Action(BuyBuild(BuildRoad(rd))) )
                          else if can_trade me g then Action(trade g me) 
                          else if should_year_of_plenty crds me then 
                                  let (res1,res2) = year_of_plenty me in 
                                  Action(PlayCard(PlayYearOfPlenty(res1,Some res2)))
                          else if should_monopoly crds g me then Action(PlayCard(PlayMonopoly(most_needed me)))
                          else if can_build_city me (!my_places) then Action(BuyBuild(BuildCity(build_city (!my_places)))) 
                          else if can_build_town me g then 
                                    let move =  Action(BuyBuild(BuildTown(build_town g me))) in 
                                    (if List.length !my_places <4 then 
                                      (current_goal:= !current_goal)
                                    else (current_goal := City) );
                                    (if not (can_build_road me g) then (current_goal := City)
                                    else (current_goal:= !current_goal));
                                    move
                          else if can_build_road me g && afford_road me then let rd = (mycolor , build_road g me) 
                                              in Action(BuyBuild(BuildRoad(rd)))
                          else if (not (!current_goal = City )) && (can_buy_card me g) then Action(BuyBuild(BuildCard))
                          else let move = Action(EndTurn) in (previous_trades := []); move
                                 )) 
                    in finalchoice
                    end

(* Do not change *)
let _ = register_bot name
  (module Bot(New)) (module Bot(New)) (module Bot(New)) (module Bot(New))
