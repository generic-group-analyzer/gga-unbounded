open Core_kernel.Std
open Abbrevs
open Wconstrs
open Wrules
open Watom
open Util

type param_list = int Atom.Map.t with compare, sexp
type idx_order_list = ivar list list with compare, sexp

let any_extracted = ref false

let all_parameters_poly poly parameters free_idxs =
  Map.fold poly
    ~init:parameters
    ~f:(fun ~key:s ~data:_c parameters' -> 
	let (p_list,_) = L.unzip (params s.monom) in
	L.fold_left p_list
	 ~init:parameters'
	 ~f:(fun parameters' p ->
	   match p with
	   | Param(name, Some i) -> 
	      if (Set.mem free_idxs i) then
		Map.change parameters' p 
	                   (function 
			   | None -> Some 1
			   | Some n -> Some (n+1)
			   )
	      else
		let p_equiv = L.find (Map.keys parameters') 
		               ~f:(function
			           | Param(name', Some i') -> name = name' && not(Set.mem free_idxs i')
				   | _ -> false
			       ) in
		begin match p_equiv with
		| None -> Map.add parameters' ~key:p ~data:1
		| Some p' -> 
		   Map.change parameters' p'
		     (function 
		     | None -> Some 1
		     | Some n -> Some (n+1)
		     )
		end
	   | Param(_, None) ->
	      Map.change parameters' p 
	                 (function 
			 | None -> Some 1
			 | Some n -> Some (n+1)
			 )
	   | _ -> assert false
	    )
       )

let all_parameters constraints =
  let free_idxs = free_ivars_constr_conj constraints in
  L.fold_left constraints
   ~init:Atom.Map.empty
   ~f:(fun parameters c -> all_parameters_poly c.poly parameters free_idxs)

let all_parameters_filtered constraints = 
  all_parameters constraints
  |> Map.filter ~f:(fun ~key:p ~data:_ -> not(known_not_null SP.(of_a p) constraints))

let extract_everything_equation constraints depth (k1,k2) counter _oc =
  let free_ivars = free_ivars_constr_conj constraints in

  let rec aux constraints monomials extracted =
    let eq = L.nth_exn constraints (counter-1) in
    let monomials =
      if extracted then
	(*let () = F.printf "[%a]\n" (pp_list "," pp_monom) (mons_hvar_free eq.poly) in
	F.printf "%a\n" pp_poly eq.poly;
	F.print_flush();*)
	L.dedup (mons_hvar_free eq.poly) ~compare:compare_monom
	  
      else monomials
    in
    if not(L.exists monomials ~f:(fun m -> not(Map.is_empty m))) then
      constraints
    else
      match monomials with
      | [] -> constraints
      | mon :: rest_monoms ->
	 let idxs = Set.to_list (Set.diff (ivars_monom mon) (Set.union free_ivars (Ivar.Set.of_list eq.qvars))) in
	 if not(overlap (idxs,mon) eq.poly k1 k2) then
	   let () = 
	     if (Map.is_empty mon) then F.printf "%sextract (;) %i.\n" (repeat_string "  " depth) counter
	     else F.printf "%sextract (%a; %a) %i.\n" (repeat_string "  " depth) (pp_list "," pp_ivar) idxs pp_monom mon counter
	   in
	   F.print_flush ();
	   any_extracted := true;
	   let new_constraints = extract_stable_nth constraints (idxs,mon) k1 k2 counter in

	   aux new_constraints [] true
	 else
	   aux constraints rest_monoms false
  in
  let eq = L.nth_exn constraints (counter-1) in
  if eq.is_eq = InEq then constraints
  else aux constraints [] true
     
let extract_everything constraints depth (k1,k2) oc =
  let rec aux constraints counter =
    if (counter > L.length constraints) then constraints
    else 
      aux (extract_everything_equation constraints depth (k1,k2) counter oc) (counter+1)
  in
  aux constraints 1
  
let automatic_algorithm system (k1,k2) oc =
  let step goals depth used_parameters_list indices_order_list =
    let constraints = L.hd_exn goals in
    let rest_goals = L.tl_exn goals in
    
    (*F.printf "[%a]\n" (pp_list "," pp_atom) (L.hd_exn used_parameters_list);
    F.print_flush ();*)

    let (contradiction, _) = Wrules.contradictions_msg (clear_equations constraints) in
    if contradiction then
      let () = F.printf "%scontradiction.\n" (repeat_string "  " depth) in
      if (L.length rest_goals > 0) then
	let constraints = L.hd_exn rest_goals in
	let rest_goals = L.tl_exn rest_goals in
	let used_parameters_list = L.tl_exn used_parameters_list in
	let indices_order_list = L.tl_exn indices_order_list in
	let (contradiction_next, _) = Wrules.contradictions_msg (clear_equations constraints) in
	if (contradiction_next) then
	  constraints :: rest_goals, depth-1, used_parameters_list, indices_order_list
	else
	  let () = F.printf "%ssimplify_vars.\n" (repeat_string "  " (depth-1)) in
	  let () = F.printf "%ssimplify_vars.\n" (repeat_string "  " (depth-1)) in
	  let () = F.printf "%ssimplify.\n" (repeat_string "  " (depth-1)) in
	  F.print_flush ();
	  (simplify (simplify_vars (simplify_vars constraints))) :: rest_goals, depth-1, used_parameters_list, indices_order_list
      else
	rest_goals, depth-1, used_parameters_list, indices_order_list
    else

    let () = any_extracted := false in
    let constraints = extract_everything constraints depth (k1,k2) oc in
    let constraints =
      if !any_extracted then
	let () = F.printf "%ssimplify_vars.\n" (repeat_string "  " depth) in
	let () = F.printf "%ssimplify_vars.\n" (repeat_string "  " depth) in
	let () = F.printf "%ssimplify.\n" (repeat_string "  " depth) in
	F.print_flush();
	simplify (simplify_vars (simplify_vars constraints))
      else
	constraints
    in

    let new_eqs = extract_every_handle_monomial_constraints constraints (L.hd_exn indices_order_list) in
    if (L.length new_eqs <> 0) then
	let () = F.printf "(* Indices trick! *)\n" in
	F.printf "(*   %a@\n*)@\n"(pp_list "@\n \\/  " pp_constr) new_eqs;
	F.print_flush();
	let new_constraints = L.map new_eqs ~f:(fun nc -> simplify (simplify_vars (introduce_branch [nc] constraints ))) in
	let k = L.length new_eqs in
	new_constraints @ rest_goals, depth+k-1,
	(repeat_element (L.hd_exn used_parameters_list) k) @ (L.tl_exn used_parameters_list),
	(repeat_element (L.hd_exn indices_order_list) k) @ (L.tl_exn indices_order_list)
    else

    (*F.printf "%a@\n" pp_constr_conj constraints;
    F.print_flush(); *)

    let (contradiction, _) = Wrules.contradictions_msg (clear_equations constraints) in
    if contradiction then constraints :: rest_goals, depth, used_parameters_list, indices_order_list
    else

    let used_parameters = L.hd_exn used_parameters_list in
    let rest_used_parameters = L.tl_exn used_parameters_list in
    let parameters = all_parameters constraints in
    let max_count = L.fold_left (Map.data parameters) ~init: 0 ~f:(fun m x -> if x > m then x else m) in
    let free_idxs = free_ivars_constr_conj constraints in
    let parameters = Map.filter (all_parameters constraints) 
                        ~f:(fun ~key:p ~data:_ ->
			  not (L.mem used_parameters p 
				 ~equal:(fun p1 p2 ->
				     match p1, p2 with
				     | Param(name1,i), Param(name2,j) ->
					if (name1 = name2) then
					  (match i,j with
					  | Some i, Some j -> 
					     if (Set.mem free_idxs i) then equal_ivar i j
					     else false
					  | _ -> true
					  )
					else false
				     | _ -> false
				 )
			  )
			)
    in
    let parameters = (* If previous case_distinction in a parameter, put it in the end of the queue *)
      Map.fold parameters 
	~init:Atom.Map.empty
        ~f:(fun ~key:p ~data:d m ->
	  if (L.mem used_parameters p 
		 ~equal:(fun p1 p2 ->
		   match p1, p2 with
		   | Param(name1,_), Param(name2,_) -> name1 = name2
		   | _ -> false
		 )
	     ) then
	    Map.add m ~key:p ~data:(d-max_count)
	  else
	    Map.add m ~key:p ~data:d
	)
    in
    let keys = Map.keys parameters in
    let data = Map.data parameters in
    let _data, parameters = quicksort_double (>) data keys in
    (*let () = F.printf "[%a]@\n" (pp_list ", " pp_atom) used_parameters in
    let () = F.printf "[%a]@\n" (pp_list ", " pp_atom) parameters in
    F.print_flush();*)
    (*let () = F.printf "[%a]@\n" (pp_list ", " pp_int) _data in*)
      match parameters with
      | [] ->
	 let new_branches = L.concat (L.map constraints ~f:simplify_single_handle_eqs) in
	 (*F.printf "%a@\n" pp_constr_conj constraints;
	 F.print_flush();*)
	 if (new_branches = [[]] || new_branches = []) then
	   let indices_order = L.hd_exn indices_order_list in
	   let free = Set.to_list (free_ivars_constr_conj constraints)
                      |> L.filter ~f:(fun i -> not(L.mem indices_order i ~equal:equal_ivar))
	   in
	   begin match free with
	   | [] -> (constraints :: rest_goals), depth+1, used_parameters_list, indices_order_list
	   | i :: _ ->
	      let new_indices = insert i indices_order in
	      let k = L.length new_indices in
	      (repeat_element constraints k) @ rest_goals, depth+k-1, (repeat_element (L.hd_exn used_parameters_list) k) @ (L.tl_exn used_parameters_list), new_indices @ (L.tl_exn indices_order_list)
	   end

	 else
	   let new_constraints = L.map new_branches ~f:(fun branch -> simplify (simplify_vars (introduce_branch branch constraints)) ) in
	   F.printf "(* If Laurent polynomial then,\n     (%a)@\n*)\n" (pp_list ")@\n \\/  (" (pp_list " /\\ " pp_constr)) new_branches;
	   F.print_flush();
	   let k = L.length new_constraints in
	   new_constraints @ rest_goals, depth+k-1, 
	   (repeat_element (L.hd_exn used_parameters_list) k) @ (L.tl_exn used_parameters_list),
	   (repeat_element (L.hd_exn indices_order_list) k) @ (L.tl_exn indices_order_list)

      | p :: _rest_parameters ->
	 let cases = case_dist constraints p in
	 let case1 = clear_non_used_idxs (L.nth_exn cases 0) in
	 let case2 = clear_non_used_idxs (L.nth_exn cases 1) in
	 let () = F.printf "%scase_distinction %a.\n" (repeat_string "  " depth) pp_atom p in
	 F.print_flush ();
	 ([case1] @ [case2] @ rest_goals), depth+1,
	 [p :: used_parameters] @ [p :: used_parameters] @ rest_used_parameters,
	 (L.hd_exn indices_order_list) :: indices_order_list
  in

  let rec aux goals depth used_parameters_list (indices_order_list : idx_order_list ) =
    if (L.length goals = 0) then true
    else if (depth = 50) then false
    else 
      let new_goals, new_depth, new_used_parameters_list, new_indices_order_list = 
	step goals depth used_parameters_list indices_order_list in
      aux new_goals new_depth new_used_parameters_list new_indices_order_list
  in
  aux system 0 [[]] [[]]

let automatic_tool cmds _file =
  let constraints, (k1,k2) = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let oc = 1234 in
  let proven = automatic_algorithm [uniform_bound constraints] (k1,k2) oc in
  if proven then
    let () =  F.printf "Proven!\n(Group order >= %d)\n" (Big_int.int_of_big_int !group_order_bound) in
    exit 0
  else
    exit 1
(*    F.printf "Not proven\n"*)

let analyze_unbounded _cmds _intrs = ()
(*
let analyze_unbounded cmds instrs =
  let file = open_out "log" in
  let shell = Unix.dup Unix.stdout in
  Unix.dup2 (Unix.descr_of_out_channel file) Unix.stdout;
  let constraints, (k1,k2) = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let (system, nth) = Eval.eval_instrs (Wparse.p_instrs instrs) (k1,k2) [constraints] 1 in
  F.print_flush ();
  close_out file;
  Unix.dup2 shell Unix.stdout;
  
  if (L.length system = 0) then
    F.printf "# Proven!\n(Group order >= %d)@\n" (Big_int.int_of_big_int !group_order_bound)

  else
    let constraints = L.nth_exn system (nth-1) in
    F.printf "Working on goal %d out of %d." nth (L.length system);  
    F.printf "%s(Group order >= %d)@\n\n" ("       ") (Big_int.int_of_big_int !group_order_bound);
    F.printf "%a" pp_constr_conj constraints;
    let (contradiction, c) = Wrules.contradictions_msg constraints in
    if contradiction then
      F.printf "Contradiction!\n%a" pp_constr c
    else ()
 *)

let analyze_unbounded_ws cmds instrs =
  let open Big_int in
  let constraints, (k1,k2) = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let (system, nth) = Eval.eval_instrs (Wparse.p_instrs instrs) (k1,k2) [constraints] 1 in

  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  begin match system with
  | [] ->
    F.fprintf fbuf "<p>Proven!\n(Group order >= %s)\n</p>" (string_of_big_int !group_order_bound)
  | _::_ ->
    let constraints = L.nth_exn system (nth-1) in
    F.fprintf fbuf 
       "<p>Working on goal %d out of %d.  (Group order >= %s)</p>\n"
       nth (L.length system) (string_of_big_int !group_order_bound);  
    F.fprintf fbuf "%a" PPLatex.pp_constr_conj_latex constraints;
    let (contradiction, c) = Wrules.contradictions_msg constraints in
    if contradiction then
      let () = F.fprintf fbuf "\n<p>Contradiction!\n</p>" in
      F.fprintf fbuf "<p><script type=\"math/tex\" mode=\"display\">%a\n</script></p>" PPLatex.pp_constr_latex c
    else ()
  end;
  F.pp_print_flush fbuf ();
  Buffer.contents buf


let string_of_state st =
  let open Big_int in
  let (system, nth) = st in
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  begin match system with
  | [] ->
    F.fprintf fbuf "<p>Proven!\n(Group order >= %s)\n</p>" (string_of_big_int !group_order_bound)
  | _::_ ->
    let constraints = L.nth_exn system (nth-1) in
    F.fprintf fbuf 
       "<p>Working on goal %d out of %d.  (Group order >= %s)</p>\n"
       nth (L.length system) (string_of_big_int !group_order_bound);  
    F.fprintf fbuf "%a" PPLatex.pp_constr_conj_latex constraints;
    let (contradiction, c) = Wrules.contradictions_msg (clear_equations constraints) in
    if contradiction then
      let () = F.fprintf fbuf "\n<p>Contradiction!\n</p>" in
      F.fprintf fbuf "<p><script type=\"math/tex\" mode=\"display\">%a\n</script></p>" PPLatex.pp_constr_latex c
    else ()
  end;
  F.pp_print_flush fbuf ();
  Buffer.contents buf
