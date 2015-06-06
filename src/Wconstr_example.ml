open Core.Std
open Abbrevs
open Watom
open Wconstrs
open Wrules

(* Example:
   Public key: [V,W]_1
   Sign([hm]_2) = [R, hm*V + W + R^2]_2,
   Win([m,r,s]_2) = forall i. m <> hm_i /\ s = m*V + W + r^2
*)


(* global random vars *)
let rV = mk_rvar "V"
let rW = mk_rvar "W"

(* ----------------------------------------------------------------------- *)
(* Rules *)

type rule =
  | ExtractStable of ivar list * monom * (monom -> monom -> bool)
  | CaseDist of atom
  | Simplify
  | Contradiction
  | Admit

let apply_rule r constrs =
  match r with
  | ExtractStable (idxs, mon, overlap) -> [extract_stable_all (idxs, mon) overlap constrs]
  | CaseDist (par) -> case_dist constrs par
  | Simplify -> [simplify constrs]
  | Contradiction -> if (contradictions constrs) then [] else [constrs]
  | Admit -> []		 

(* Oracle *)
let i = { name = "i"; id = 0 }
let j = { name = "j"; id = 0 }
let hm i = mk_hvar ~idx:i G2 "m"
let rR (i : ivar) = mk_rvar ~idx:(Some i) "R"

let lincomb idx p1 p2 p3 =
  SP.(
    let p1 = of_a p1 in
    let p2_j = of_a (p2 idx) in
    let p3_j = of_a (p3 idx) in
    let rV = of_a rV in
    let rW = of_a rW in
    let rR_j = of_a (rR idx) in
    let hm_j = of_a (hm idx) in

    p1 +!
    sum [idx] (p2_j *! rR_j) +!
    sum [idx] (p3_j *! (hm_j *! rV +! rW +! (rR_j *! rR_j)))
  )

let pm   = mk_param "pm"
let pmR i = mk_param ~idx:(Some i) "pmR"
let pmS i = mk_param ~idx:(Some i) "pmS"
let wm = lincomb j pm pmR pmS

let hm_spoly i = SP.of_a (hm i)

let m_constr = mk_constr [i] [] InEq SP.(wm -! hm_spoly i)
				       
let ps   = mk_param "ps"
let psR i = mk_param ~idx:(Some i) "psR"
let psS i = mk_param ~idx:(Some i) "psS"
let ws = lincomb j ps psR psS

let pr   = mk_param "pr"
let prR i = mk_param ~idx:(Some i) "prR"
let prS i = mk_param ~idx:(Some i) "prS"
let wr = lincomb j pr prR prS

let s_constr =
  let rV = SP.of_a rV in
  let rW = SP.of_a rW in
  mk_constr [] [] Eq SP.((wr *! wr) +! (wm *! rV) +! rW -! ws)


let unit_monom = mk_monom []
let k1 = { n = [unit_monom]; r =[]; rj =[]}
let k2 = { n = [unit_monom; (mk_monom [(NoInv,rR i)]) ; (mk_monom [(NoInv,rW)])];
	  r =[(mk_monom [(NoInv,rV)])]; rj =[]}

let system = [m_constr; s_constr]
	   
let monomials = mons m_constr.poly

let _n = overlap (List.nth_exn monomials 0) (mult_monom (List.nth_exn monomials 1) (List.nth_exn monomials 1)) k1 k2

		 
let rec print_int_list = function
  | [] -> ()
  | a :: rest -> let () = print_string ((string_of_int a) ^ " ") in print_int_list rest

let rec print_int_list_list = function
  | [] -> ()
  | a :: rest -> let () = print_int_list a in
		 let () = print_string "\n" in
		 print_int_list_list rest	    
		  								   
  (*		 
let () =
  F.printf "%a" pp_constr_conj system ;
  let system2 = subst system pm (SP.(one)) in
  F.printf "%a" pp_constr_conj system2 ;
  let system3 = subst_bound_by_zero system (pmR j) in
  F.printf "%a" pp_constr_conj system3
  *)
  (*
  F.printf "[%a]\n" (Util.pp_list ", " pp_monom) monomials ;
  F.printf "[%a]\n" (Util.pp_list ", " pp_monom) (mons_sets_product monomials  monomials) ;
  F.printf "%a\n" pp_poly (coeff m_constr.poly (List.nth_exn monomials 3)) ;
   *)
				     
let pp_renaming rn =
  let () = print_string "Renaming:\n" in
  Map.iter rn ~f:(fun ~key:k ~data:v -> F.printf "(%a |-> %a)\n" pp_ivar k pp_ivar v)
	   
let rec pp_perms = function
  | [] -> F.printf "\n"
  | p :: rest -> F.printf "%a\n" (Util.pp_list "," pp_ivar) p; pp_perms rest
	   
let () =

  (* Examples *)
  let c1 = Wparse.constr "(sum i,j: p_i*r_j^2) + (sum k: p_k*p_l) = 0" in
  let c2 = Wparse.constr "(sum k: p_k*p_l) + (sum k,j: p_j*r_k^2) = 0" in
  let _c3 = Wparse.constr "forall k,l,lzzz: (sum i: p_i*p_k) + h_l@2 <> 0" in
  let c4 = Wparse.constr "-1 * (sum i: p_i) * (sum i: p_i) = 0" in
  let c5 = Wparse.constr "(sum l1: p_l1) * (sum k: p_k) = 0" in
  let c6 = Wparse.constr "(sum i,j,k: p_i * r_i*r_j*r_k) = 0" in
  let c7 = coeff c6.poly (L.map ["i";"j";"k"] ~f:Wparse.ivar, Wparse.monom "r_i*r_j*r_k") in
  let c8 = Wparse.poly "2 * (p_i + p_j + p_k)" in
  let c9 = Wparse.constr "(sum i: p_i*r_k) = 0" in
  let c10 = Wparse.constr "(sum i: p_i*r_j) = 0" in

  (*
  F.printf "%a" pp_constr c1;
  F.printf "%a\n" pp_constr c2;
  F.printf "%a" pp_constr_conj (all_ivar_distinct_constr_conj [_c3]);
  F.printf "%a" pp_constr c4;
  F.printf "%a\n" pp_constr c5;
  F.printf "%a\n" pp_constr c6;
  F.printf "%a\n" pp_poly c7;
  F.printf "%a" pp_poly c8;
   *)
  
  assert(isomorphic_constr c1 c2);
  assert(isomorphic_constr c4 c5);
  assert(isomorphic_poly c7 c8);
  assert(not (isomorphic_constr c9 c10))



type proof = Pr of constr_conj * (rule * proof list) option

type position = int list
						     
let rec get_goals = function
  | Pr (constrs, None) -> [constrs]
  | Pr (_, Some (_, pr_list)) -> L.concat (L.map ~f:get_goals pr_list)
					  
let rec get_pos = function
  | Pr (_, None) -> []
  | Pr (_, Some (_, pr_list)) ->
     L.map2_exn (Util.range 0 ((L.length pr_list)-1))
		(L.map pr_list ~f:get_pos)
		~f:(fun a l -> L.concat (L.map l ~f:(fun l' -> a :: l')))

let rec set_pos pr r = function
  | [] ->
     begin match pr with
     | Pr (constrs, None) ->
	let sub_pr = L.map (apply_rule r constrs) ~f:(fun c -> Pr (c, None)) in
	Pr (constrs, Some (r, sub_pr))
     | _ -> failwith "set_pos: invalid position for the proof tree"
     end
  | p :: rest_pos ->
     begin match pr with
     | Pr (_, None) -> failwith "set_pos: invalid position for the proof tree"
     | Pr (constrs, Some (r', pr_list)) ->
	Pr (constrs, Some (r', Util.list_map_nth pr_list p (fun x -> set_pos x r rest_pos)))
     end

let show_goal_nth n pr =
  let goals = get_goals pr in
  F.printf "\nWorking on goal %d out of %d." n (L.length goals);
  F.printf "%s(Group order >= %d)@\n\n" ("       ") (Big_int.int_of_big_int !group_order_bound);
  F.printf "%a" pp_constr_conj (L.nth_exn goals n)

let modify_goal_nth n r pr =
  let pos = L.nth_exn (get_pos pr) n in
  set_pos pr r pos



let proof_state = ref [system]
let n_system = ref 1

	  
let instruction name ?(id = 1) ?(idxs = []) ?(m = "") ?(p = "") () =
  match name with
  | "EXTRACT" ->
     let f system = extract_stable_nth system (L.map idxs ~f:Wparse.ivar, Wparse.monom m) k1 k2 id
		    |> simplify
     in
     proof_state := Util.list_map_nth !proof_state !n_system f
				      
  | "CASE_DISTINCTION" ->
     let cases = case_dist (L.nth_exn !proof_state (!n_system - 1)) (Wparse.atom p) in
     let case1 = simplify (L.nth_exn cases 0) in
     let case2 = simplify (L.nth_exn cases 1) in
     proof_state := (Util.list_map_nth !proof_state !n_system (fun _ -> case1)) @ [case2]

  | "CHANGE_GOAL" ->
     if (id >= 0 && id <= L.length !proof_state) then n_system := id
     else failwith "instruction: wrong identifier"

  | "SOLVED_GOAL" ->
     proof_state := Util.list_remove !proof_state !n_system;
     n_system := 1;
						    
  | "SIMPLIFY" ->
     proof_state := Util.list_map_nth !proof_state !n_system simplify
				      
  | _ -> failwith "instruction: unknown command"

let pp_proof_state () =
  F.printf "\nWorking on goal %d out of %d." !n_system (L.length !proof_state);  
  F.printf "%s(Group order >= %d)@\n\n" ("       ") (Big_int.int_of_big_int !group_order_bound);
  let system = (L.nth_exn !proof_state (!n_system - 1)) in
  F.printf "%a" pp_constr_conj system;
  if contradictions system then print_string "Contradiction!\n\n"
  else ()

let () =

  instruction "EXTRACT" ~id:2 ();
  instruction "EXTRACT" ~id:2 ~idxs:["i"] ~m:"R_i" ();
  instruction "EXTRACT" ~id:2 ~idxs:["i"] ~m:"R_i^2" ();
  instruction "EXTRACT" ~id:2 ~idxs:["i"] ~m:"R_i^3" ();
  instruction "EXTRACT" ~id:2 ~idxs:["i"] ~m:"R_i^4" ();
  instruction "EXTRACT" ~id:2             ~m:"W" ();
  instruction "EXTRACT" ~id:2             ~m:"W^2" ();
  instruction "EXTRACT" ~id:2 ~idxs:["i"] ~m:"R_i*W" ();
  instruction "EXTRACT" ~id:2 ~idxs:["i"] ~m:"R_i^2*W" ();
  instruction "EXTRACT" ~id:2 ~idxs:["i";"j"] ~m:"R_i*R_j" ();
  instruction "EXTRACT" ~id:2 ~idxs:["i";"j"] ~m:"R_i*R_j^2" ();
  instruction "EXTRACT" ~id:2 ~idxs:["i";"j"] ~m:"R_i^2*R_j^2" ();
    
  instruction "CASE_DISTINCTION" ~p:"prR_i" ();  
  instruction "SOLVED_GOAL" ();
  
  instruction "SIMPLIFY" ();  
  instruction "SOLVED_GOAL" ();
  

  if (L.length !proof_state = 0) then F.printf "\nProven!\n"
  else  pp_proof_state ()
 
