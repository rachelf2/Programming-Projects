(*This is a the game layout to Settlers of Catan. It takes inputs from a bot and restructures the board in order to 
update it to the current standings according the move*)

open Definition
open Constant
open Util
open Print
open GameUtil

(* Just a state right now *)

type game = GameUtil.game

let state_of_game g = 
	let turnnew 	= g.turn in 
	let structnew 	= ( g.board.structures.intersection_list, g.board.structures.road_list) in 
	let playernew 	= (List.fold_right (fun (ele:playerg) acc -> (	ele.color,
																	(ele.hand.inventory, ele.hand.cards),
																	ele.trophies)::acc)
										(g.playerlist : playerg list) [] ) in
	let nextnew 	= (g.next.color, g.next.request) in
	let portsnew 	= (List.fold_right 	(fun ele acc -> (ele.line, ele.ratio, ele.portresource)::acc)
										g.board.map.port []) in
	let mapnew 		= (g.board.map.hex_list, portsnew) in 
	let boardnew 	= (mapnew, structnew, g.board.deck, g.board.discard, g.board.robber) in 

	(boardnew,playernew,turnnew,nextnew)
	

let game_of_state (s : state)  = 
	let structnew =
	match s with
		|(b,pl,t,n) -> 
		match b with 
			|(map,structures,deck,discard,robber) -> 
			match structures with
				|(intlst,rdlst)-> {intersection_list= intlst; road_list=rdlst} in
	let playernew= 
	match s with 
		|(b,pl,t,n) -> (List.fold_right (fun ele acc-> match ele with
											|(color,(inventory,cards),trophies) -> 
												{color = color; hand = {inventory = inventory; cards= cards};trophies = trophies}
												::acc ) pl []) in
	let mapnew = 
	match s with
		|(b,pl,t,n) -> 
		match b with
			|(map,str,dec,dis,rob)-> 
			match map with
				|(hexlst, prtlist) -> 
						let newprtlist = List.fold_right 
										(fun ele acc -> 
											match ele with
												|(l,r,pr) -> {line = l; ratio = r; portresource = pr}::acc ) prtlist [] in
						{hex_list = hexlst; port = newprtlist} in 
	let nextnew = 
	match s with
		|(b,pl,t,n) -> 
		match n with 
			|(color,request) -> {color = color; request = request} in
	let boardnew = 
	match s with
		|(b,pl,t,n) -> 
		match b with 
				|(map, struc, deck, disc, robber)-> {map = mapnew; structures = structnew; deck = deck; discard = disc; robber = robber}
			in
	let turn = match s with
		|(b,pl,t,n) -> t in 

	{board = boardnew; playerlist = playernew; turn = turn; next = nextnew}


let init_game () = game_of_state (gen_random_initial_state())


let rec handle_move g m = 
  let (b,_,_,_) = state_of_game g in 
  let str = (print_board b) in 
  print_endline(str); 
	let activeplayer = g.next.color in 
	let current_player = find_player activeplayer g.playerlist in

	match m with
		  | InitialMove(line) -> 	if not (check_initial_move line g.board) then random_initial g
									else
                    let (r1,r2) = line in 
                    if ((r1 < cMIN_POINT_NUM || r1 > cMAX_POINT_NUM) || r2 < cMIN_POINT_NUM) || r2 > cMAX_POINT_NUM then random_initial g
                      else
		  							let newinters = 
		  								match line with 
		  								| (p1,p2) -> (update_inters g.board.structures.intersection_list p1 activeplayer []) in 
		  							let newstruct = {	intersection_list = newinters; 
		  												road_list = (activeplayer, line) :: g.board.structures.road_list 
		  											} in 
		  							
		  							let newplayer = initial_move_resource_update current_player g (fst(line)) in 
		  							let new_playerlist = replace_player g.playerlist newplayer in 
		  							let  (newnext : nextg)  = 	(let num_settlements = (list_count (fun x -> match x with 
		  																	|None -> false
		  																	|_-> true) newstruct.intersection_list )
		  											in 
		  											if num_settlements < 4 then {color = next_turn activeplayer ; request = InitialRequest}
                            else if num_settlements < 5 then {color = activeplayer; request = InitialRequest} 
		  											else if num_settlements < 8 then {color = prev_turn activeplayer ; request = InitialRequest}
		  											else {color = activeplayer ;  request = ActionRequest} ) in
		  							let newgame = {g with board = {g.board with structures = newstruct} ; playerlist = new_playerlist ; next = newnext}
		  							in check_win newgame

          | RobberMove(piece,color) -> 	
                          if piece > cMAX_PIECE_NUM || piece < cMIN_PIECE_NUM then random_robber g else
                          if not (check_robber_move piece color g.board activeplayer) then random_robber g else
	          							let newboard = {g.board with robber = piece} in
	          							if is_none color 
	          								then (check_win {g with board = newboard ; next = {color = activeplayer ;  request = ActionRequest}}) 
	          							else
		          							let color  = get_some color 
		          							in 
		          							let victim = find_player color g.playerlist in 
		          							let victiminv = victim.hand.inventory in 
		          							if (sum_cost victiminv) = 0 then (check_win {g with board = newboard; next = {color = activeplayer ;  request = ActionRequest} }) 
		          							else
		          							let activeplay = find_player activeplayer g.playerlist in 
		          							let decrement = 
		          							  (match victiminv with 
		          							  | (b,w,o,g,l) -> find_resource [1;2;3;4;5] (b,w,o,g,l) ) in 
		          							let newactive = add_to_inventory activeplay (single_resource_cost decrement) in
		          							let newvictim = sub_from_inventory victim (single_resource_cost decrement) in
											let newplayerlist = replace_player (replace_player g.playerlist newvictim) newactive in
											let newgame = {g with board = newboard ; playerlist = newplayerlist ; next = {color = activeplayer ;  request = ActionRequest}} in 
											check_win newgame 
										
          | DiscardMove(cb,cw,co,cg,cl)-> 	let fixed_cost = fix_discard (cb,cw,co,cg,cl) current_player.hand.inventory in
     										let working_inv = adjust_cost_for_rob fixed_cost g current_player in
											let newplayer = sub_from_inventory current_player working_inv in
          									let newplayerlist = replace_player g.playerlist newplayer in 
          									let newnext = 	if (not (is_none g.turn.dicerolled)) && (get_some(g.turn.dicerolled) = cROBBER_ROLL) 
          												then 
          													(match (next_player_robbed (find_player (next_turn activeplayer) newplayerlist) (find_player g.turn.active newplayerlist) newplayerlist) with 
          														|None -> {color = g.turn.active ; request = RobberRequest}
          														|Some c -> {g.next with color = c} )
          												else {color = g.turn.active ; request = ActionRequest}
          								 	in 
          									let newgame = {g with playerlist = newplayerlist; next = newnext} in  
          									check_win newgame         													
          
          | TradeResponse(bol)-> if (bol = false) then (** true to accept the trade, false to reject. *)
	          						
	          						let newturn = {g.turn with tradesmade = (g.turn.tradesmade +1) ; pendingtrade = None } in 
	          						let newgame = {g with turn = newturn ; next = {color = newturn.active ; request = ActionRequest}} in 
	          						check_win newgame
          						else
          							let trade = g.turn.pendingtrade in 
          							(match trade with 
          								|None -> failwith "this shouldn't happen"
          								| Some (color, c1, c2) -> 
          								let partner = find_player color g.playerlist in 
          								let active_player = find_player g.turn.active g.playerlist in
          								let new_partner = add_to_inventory (sub_from_inventory partner c2) c1 in 
          								let new_active = add_to_inventory (sub_from_inventory active_player c1) c2 in 
          								let new_playerlist = replace_player (replace_player g.playerlist new_active) new_partner in 
	          						let newturn = {g.turn with tradesmade = g.turn.tradesmade +1; pendingtrade = None} in
	          						let newgame = {g with turn = newturn; playerlist = new_playerlist ; next = {color = newturn.active ; request = ActionRequest}} in
	          						check_win newgame )


          | Action(action) ->  (match action with
          	| RollDice -> 	if not (check_rolldice g) then random_action g
          					else
          					let roll = random_roll () in
          					let roll_updated_game = {g with turn = {g.turn with dicerolled = Some roll} } in
          					if roll = cROBBER_ROLL then (match active_player_discard g.turn.active g.playerlist with 
          						|None -> check_win {roll_updated_game with next = {color = activeplayer ; request = RobberRequest}}
          						|Some c -> check_win { roll_updated_game with next = {color = c ; request = DiscardRequest}} )
          					else let newgame = {roll_updated_game with playerlist = (generate_resources roll roll_updated_game) }
          					in check_win (newgame : game) 
            | MaritimeTrade(maritimeresource)-> let ratio_opt = (borders_port g.board.map.port activeplayer (fst(maritimeresource)) g.board) in
            									let ratio = if is_none ratio_opt then cMARITIME_DEFAULT_RATIO else get_some ratio_opt in
            								 	let (sold,bought) = maritimeresource in
            								 	let added_inv= add_to_inventory current_player (single_resource_cost bought) in
            								 	let newcost = map_cost (fun a-> ratio*a) (single_resource_cost sold) in 
            								 	let newpl= sub_from_inventory added_inv newcost in
            								 	if is_neg newpl.hand.inventory then random_action g
            								 	else 
          										(let newplayerlist = (replace_player g.playerlist newpl) in 
          										let newgame = {g with playerlist = newplayerlist} in
          										check_win newgame)       					
            | BuyBuild(build) -> (match build with
            	|BuildRoad(road) -> 
                                let (color,(p1,p2)) = road in 
                                let roadlist = g.board.structures.road_list in
                                if ((p1 < cMIN_POINT_NUM || p1 > cMAX_POINT_NUM) || p2 < cMIN_POINT_NUM) || p2 > cMAX_POINT_NUM then random_action g
                                else
                                let can_build = List.mem p2 (adjacent_points p1) && p2 <> p1 in
                                let connected_point = is_connected roadlist road in 
                                let already_built = road_already_built roadlist road in
                                if not (can_build && connected_point && (not already_built)) then random_action g
                                else 
                                if not (not_through_settlement (p1,p2) activeplayer g.board.structures.intersection_list roadlist)
                                      then random_action g else 
                                let newplay = sub_from_inventory current_player cCOST_ROAD in 
                                if is_neg newplay.hand.inventory then random_action g
                                else
                                if count_roads activeplayer roadlist = cMAX_ROADS_PER_PLAYER then random_action g
                                else
                                let newroads = road::roadlist in 
                                let newplayerlist = replace_player g.playerlist newplay in 
                                let newstructures = {g.board.structures with road_list = newroads} in 
                                let newboard = {g.board with structures = newstructures} in
                                let finalgame = {g with board = newboard; playerlist = newplayerlist} in
                                check_win (check_trophies finalgame activeplayer newplay)

           		|BuildTown(point) -> if point < cMIN_POINT_NUM || point > cMAX_POINT_NUM then random_action g
                                  else
                                  if not (valid_town_location point g.board activeplayer) then random_action g 
                                  else
                                  let intlst = g.board.structures.intersection_list in
                                  if (count_towns activeplayer intlst) = cMAX_TOWNS_PER_PLAYER then random_action g
                                  else
                                  let newplay = sub_from_inventory current_player cCOST_TOWN in 
                                  if is_neg newplay.hand.inventory then random_action g 
                                  else 
                                  let newinters = update_inters g.board.structures.intersection_list point activeplayer [] in
                                  let newstructs = {g.board.structures with intersection_list = newinters} in 
                                  let newboard = {g.board with structures = newstructs} in 
                                  let newplayerlist = replace_player g.playerlist newplay in 
                                  let newgame = {g with playerlist = newplayerlist; board = newboard} in 
                                  check_win newgame
           		|BuildCity(point) -> if point < cMIN_POINT_NUM || point > cMAX_POINT_NUM then random_action g
                                  else 
                                  let inters = g.board.structures.intersection_list in 
                                  if not (check_town point activeplayer inters) then random_action g
                                  else 
                                  if count_cities activeplayer inters = cMAX_CITIES_PER_PLAYER then random_action g
                                  else 
                                  let newpl = sub_from_inventory current_player cCOST_CITY in 
                                  if is_neg newpl.hand.inventory then random_action g
                                  else
                                  let newi = (update_inters_city inters point activeplayer []) in
                                  let newstructs = {g.board.structures with intersection_list = newi} in 
                                  let newboard = {g.board with structures = newstructs} in 
                                  let newplayerlist = replace_player g.playerlist newpl in 
                                  let newgame = {g with playerlist = newplayerlist; board = newboard} in 
                                  check_win newgame

           		|BuildCard -> if not (check_card_purchase g.board.deck current_player ) then random_action g
           						else 
           						let (chosen_card , newdeck) = pick_one (reveal g.board.deck) in 
           						let new_inv_player = sub_from_inventory current_player cCOST_CARD in 
           						let new_cardsbought = append_card g.turn.cardsbought chosen_card in
           						let newgame = {	board 		= {g.board with deck = wrap_reveal(newdeck)} ;
           										playerlist 	= (replace_player g.playerlist new_inv_player);
           										turn = {g.turn with cardsbought = new_cardsbought} ;
           										next = {color = activeplayer; request = ActionRequest}
           										} in
           						check_win newgame
           		)
            | DomesticTrade(col,cost1,cost2) ->     let activepl = sub_from_inventory current_player cost1 in
            										let otherpl = sub_from_inventory (find_player col g.playerlist) cost2 in
            										let ( illegaltrade : bool) = if g.turn.tradesmade > cNUM_TRADES_PER_TURN then true else false in
            										if is_neg activepl.hand.inventory || (is_neg otherpl.hand.inventory || illegaltrade) 
            													then random_action g
            										else 
            										let newturn = {g.turn with pendingtrade = Some (col,cost1,cost2)} in
            										let newnext = {color = col; request = TradeRequest} in
            										let newgame = {g with turn = newturn; next= newnext} in
            										check_win newgame

            | PlayCard(playcard) -> 
                        let typeofcard = card_of_playcard playcard 
            						in
            						
                        let cardlist = match current_player.hand.cards with
            							|Reveal(cards) -> cards
            							|_ -> failwith "cards need to be revealed"
            						in
            						if g.turn.cardplayed = true then random_action g
                        else 
                        let newturn = {g.turn with cardplayed = true} in 
                        if not (List.mem (typeofcard) cardlist) then random_action g
            						else
            						let newcards = list_memremove (fun x -> x=typeofcard) cardlist in 
            						let newhand = {current_player.hand with cards = Reveal(newcards)} in 
            						let newplayer = {current_player with hand = newhand} in 
            						let newplayerlist = (replace_player g.playerlist newplayer) in 
            						let newdiscard = typeofcard::g.board.discard in 
                        let newboard = {g.board with discard = newdiscard} in 
                        let newgame = {g with playerlist = newplayerlist; turn = newturn; board = newboard} in 
                        let activeplayer = newgame.next.color in 
                        let current_player = find_player activeplayer newgame.playerlist in
            						
            				    (match playcard with 
            						| PlayKnight(robbermove) ->  
            							let newgame = snd(handle_move newgame (RobberMove(robbermove))) in 
            							let newnext = newgame.next in 
            							let newtrophies = match current_player.trophies with 
            								|(army,rd,ar)-> (army+1, rd, ar) in 
            							let nplayer = {current_player with trophies = newtrophies} in 
            							let newplayl = (replace_player newgame.playerlist nplayer) in
            						 	let newgame = {newgame with playerlist = newplayl; next = newnext} in
            						 	(* (print_endline "playknight trophy response"); *)
            							let finalgame = check_trophies newgame activeplayer nplayer in
            							check_win finalgame 
              					| PlayRoadBuilding(road1,roadopt) -> 
                                let (color,(p1,p2)) = road1 in 
                                let roadlist = g.board.structures.road_list in
                                let can_build = List.mem p2 (adjacent_points p1) && p2 <> p1 in
                                if ((p1 < cMIN_POINT_NUM || p1 > cMAX_POINT_NUM) || p2 < cMIN_POINT_NUM) || p2 > cMAX_POINT_NUM 
                                then random_action g else
                                let connected_point = is_connected roadlist road1 in 
                                let already_built = road_already_built roadlist road1 in 
                                if not (can_build && connected_point && (not already_built)) then random_action g
                                    else 
                                    if not (not_through_settlement (p1,p2) color g.board.structures.intersection_list roadlist)
                                      then random_action g else
                                    if count_roads activeplayer roadlist = cMAX_ROADS_PER_PLAYER then random_action g
                                    else
                                    let newroadlist = road1::roadlist in
                                    let newstructures = {newgame.board.structures with road_list = newroadlist} in 
                                    let newboard = {newgame.board with structures = newstructures} in
                                    let secondgame = {newgame with board = newboard} in
                                let finalgame = if is_none roadopt then secondgame else
                                    let (c,(r1,r2)) = get_some roadopt in
                                    let can_build2 = List.mem r2 (adjacent_points r1) && r2 <> r1 in
                                    let connected_point2 = is_connected newroadlist (get_some roadopt) in
                                    let already_built2 = road_already_built newroadlist (get_some roadopt) in
                                    if not (can_build2 && connected_point2 && (not already_built2)) then snd(random_action g)
                                    else 
                                    if not (not_through_settlement (r1,r2) activeplayer g.board.structures.intersection_list newroadlist)
                                      then snd(random_action g) else
                                    if count_roads activeplayer newroadlist = cMAX_ROADS_PER_PLAYER then snd(random_action g)
                                    else
                                    let secondroadlist = (get_some roadopt)::newroadlist in
                                    let secstruct = {secondgame.board.structures with road_list = secondroadlist} in
                                    let secboard = {secondgame.board with structures = secstruct} in
                                      {secondgame with board = secboard} in
                                check_win (check_trophies finalgame activeplayer newplayer)
              					| PlayYearOfPlenty(resource1,resourceopt) -> 
                                let newplayer = add_to_inventory current_player (single_resource_cost(resource1)) in 
                                let finalplayer = if is_none resourceopt then newplayer else
                                                add_to_inventory newplayer (single_resource_cost(get_some(resourceopt))) in 
                                let newplayerlist = replace_player newgame.playerlist finalplayer in
                                let finalgame = {newgame with playerlist = newplayerlist} in 
                                check_win finalgame
              					| PlayMonopoly(resource) -> 
                                let (newplayerlist,num_resources) = delete_resources newgame.playerlist resource in
                                let (b,w,o,g,l) = current_player.hand.inventory in 
                                let newinventory =
                                  (match resource with
                                  |Brick -> (num_resources,w,o,g,l)
                                  |Wool-> (b,num_resources,o,g,l)
                                  |Ore -> (b,w,num_resources,g,l)
                                  |Grain -> (b,w,o,num_resources,l)
                                  |Lumber -> (b,w,o,g,num_resources) )
                                in
                                let newhand = {newhand with inventory = newinventory} in 
                                let newplayer = {current_player with hand = newhand} in
                                let newplayerl = (replace_player newplayerlist newplayer) in 
                                let finalgame = {newgame with playerlist = newplayerl} in 
                                  check_win finalgame
                          )
            | EndTurn -> 
                  if is_none (g.turn.dicerolled) then random_action g else
                  let cardsbought = g.turn.cardsbought in 
                  let cb = match cardsbought with  
                      |Reveal(c)-> c
                      |Hidden(i)-> failwith "shouldnt be hidden"
                  in 
                  let cards = current_player.hand.cards in 
                  let crds = match cards with 
                      |Reveal(c) -> c
                      |Hidden(i) -> failwith "shouldnt be hidden"
                  in 
                  let newcards = crds@cb in 
                  let newhand = {current_player.hand with cards = Reveal(newcards)} in 
                  let newplayer = {current_player with hand = newhand} in 
                  let newplayerlist = replace_player g.playerlist newplayer in 
            			let newnext = {color = (next_turn activeplayer); request = ActionRequest} in
            			let newgame = {g with next = newnext; turn = new_turn newnext.color; playerlist = newplayerlist} in 
            			check_win newgame
                )
and random_action g = if is_none (g.turn.dicerolled) then handle_move g (Action(RollDice))
                      else handle_move g (Action(EndTurn))
and random_initial g = let p1 = (Random.int cNUM_POINTS) in 
                       let p2 = get_some (pick_random (adjacent_points p1)) in 
                       handle_move g (InitialMove(p1,p2))
and random_robber g = let piece = (Random.int cNUM_PIECES) in 
                      handle_move g (RobberMove(piece,None))

let presentation g = 
            let activeplayer = g.next.color in 
            let players = g.playerlist in 
            let newplayers = hide_cards activeplayer players in 
            let newdeck = hide g.board.deck in 
            let newboard = {g.board with deck = newdeck} in
            {g with playerlist = newplayers; board = newboard}
