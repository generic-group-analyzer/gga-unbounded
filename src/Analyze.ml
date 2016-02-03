open Core_kernel.Std
open Abbrevs
open Util
open Watom
open Wconstrs
open WconstrsUtil
open Wrules

type proof_branch = {
  branch_conj : conj;
  branch_used_params : atom list * string list;
  branch_free_ivars_order : ivar list;
  branch_unfolded_hvars : hvar list;
  branch_coeff_only_if_simp : bool;
} with compare, sexp

(* data structures with proof branches *)
module Proof_branch = struct
  module T = struct
    type t = proof_branch
    let compare = compare_proof_branch
    let sexp_of_t = sexp_of_proof_branch
    let t_of_sexp = proof_branch_of_sexp
  end
  include T
  include Comparable.Make(T)
end

let equal_proof_branch b1 b2 = compare_proof_branch b1 b2 = 0

let mk_proof_branch conj used_params ivars_order unfolded_hvars only_if_simp =
  { branch_conj = conj; 
    branch_used_params = used_params;
    branch_free_ivars_order = ivars_order;
    branch_unfolded_hvars = unfolded_hvars;
    branch_coeff_only_if_simp = only_if_simp;
  }

let coeff_everywhere_constr (depth : int ) (c : constr) (n : int)  advK (only_if_simp : bool) (conj : conj) =
  let context = conj.conj_ivarsK in
  let used_ivars = Set.union (Ivar.Set.of_list (unzip1 context)) (ivars_constr c) in
  let c_bound_ivars = Set.diff (ivars_constr c) (Ivar.Set.of_list (unzip1 context)) in
  let (rn,_) = renaming_away_from used_ivars c_bound_ivars in
  let ivars_context = (unzip1 context) in
  try
(*    match L.filter (mons c.constr_poly) ~f:(fun m -> equal_monom m (uvars_monom m)) with *)
    match L.map (mons c.constr_poly) ~f:(fun m -> (uvars_monom m))
          |> L.dedup ~compare:compare_monom
    with
    | [] -> []
    | m :: [] when equal_monom m (mk_monom []) -> []
    | monomials ->
      L.fold_left monomials
        ~init:[]
        ~f:(fun l m ->
            let m = map_idx_monom ~f:(apply_renaming rn) m in
            let bound_ivars =
              Set.to_list (Set.filter (ivars_monom m) ~f:(fun i -> not(L.mem (ivars_context) i)))
            in
            let quant = Eval.maximal_quant ivars_context [] bound_ivars in
            let new_constrs = introduce_coeff c quant (mon2umon m) context
                              |> L.map ~f:(fun c -> simplify_coeff_constr c context advK)
            in
            if L.exists ~f:(fun c -> L.mem conj.conj_constrs c ~equal:equal_constr) new_constrs then l
            else
              if only_if_simp && (L.exists new_constrs ~f:(fun c -> contains_coeff_constr c)) then l
              else
                let () = F.printf "%scoeff(%a) %d.\n" (String.make depth ' ') pp_monom m n in
                F.print_flush();
                l @ new_constrs
          )
  with _ -> []

let introduce_coeff_everywhere (depth : int) (advK : advK) (only_if_simp : bool) (conj : conj) =
  let rec aux new_constrs n = function
    | [] -> new_constrs
    | c :: rest ->
      if (c.constr_is_eq = Eq) then
        aux (new_constrs @ (coeff_everywhere_constr depth c n advK only_if_simp conj)) (n+1) rest
      else
        aux new_constrs (n+1) rest
  in
  mk_conj conj.conj_ivarsK (conj.conj_constrs @ (aux [] 1 conj.conj_constrs))

let divide_by_every_variable (depth : int) (conj : conj) =
  let rec aux conj = function
    | [] -> conj
    | v :: rest ->
      let conj = clear_trivial conj in
      let conj', divided = divide_conj_by v conj in
      if not divided then aux conj rest
      else
        let () = F.printf "%sdivide_by_var %a.\n" (String.make depth ' ') pp_atom v in
        aux conj' (v :: rest)
  in
  let vars = Set.filter (get_atoms_conj conj) ~f:(function | Uvar(_,None) -> true | _ -> false) in
  aux conj (Set.to_list vars)

let get_not_null_params (conj : conj) =
  L.fold_left conj.conj_constrs
   ~init:[]
   ~f:(fun l c ->
       match (Map.to_alist c.constr_poly.poly_map), c.constr_is_eq with
       | (s,_) :: [], InEq ->
         begin match s.sum_ivarsK, s.sum_summand with
           | [], Mon(mon) ->
             begin match Map.to_alist mon.monom_map with
               | (Param(name, Some i), _) :: [] ->
                 if (L.mem (unzip1 conj.conj_ivarsK) i ~equal:equal_ivar)
                 then l @ [Param(name, Some i)]
                 else l
               | (Param(name, None), _) :: [] -> l @ [Param(name, None)]
               | _ -> l
             end
           | _ -> l
         end
       | _ -> l
     )

let divide_by_not_null_params (depth : int) (conj : conj) =
  let rec aux conj = function
    | [] -> conj
    | p :: rest ->
      let conj = clear_trivial conj in
      let conj', divided = divide_conj_by p conj in
      if not divided then aux conj rest
      else
        let () = F.printf "%sdivide_by_param %a.\n" (String.make depth ' ') pp_atom p in
        aux conj' (p :: rest)
  in
  aux conj (get_not_null_params conj)

let rec count_atom (counter : int) (p : atom) = function
  | [] -> counter
  | c :: rest ->
    if Set.mem (get_atoms_constr c) p then count_atom (counter+1) p rest
    else count_atom counter p rest

let parameters_to_split (branch : proof_branch) (free_indices : ivar list) =
  (* let i = { name = new_name (L.map (Set.to_list (ivars_conj branch.branch_conj)) ~f:(fun i -> i.name)); id = 0 } in *)

  let parameters = Set.to_list (get_atoms_conj branch.branch_conj)|> L.filter ~f:is_param in
  let frequencies = L.map parameters ~f:(fun p -> count_atom 0 p branch.branch_conj.conj_constrs) in
  let (_, sorted_params) = quicksort_double (>) frequencies parameters in

  let not_bound_params, bound_params = branch.branch_used_params in

  L.fold_left sorted_params
   ~init:[]
   ~f:(fun l p ->
        match p with
        | Param(_, None) ->
          if not(L.mem not_bound_params p ~equal:equal_atom) then l @ [p]
          else l
        | Param(name, Some j) ->
          if L.mem free_indices j ~equal:equal_ivar then
            if not(L.mem not_bound_params p ~equal:equal_atom) then l @ [p]
            else l
          else
            if not(L.mem bound_params name ~equal:String.equal) && (L.length free_indices <= 1) then l @ [p]
            else l
        | _ -> assert false
      )

(*
  L.fold_left sorted_params
   ~init:([],[])
   ~f:(fun (l1,l2) p ->
        match p with
        | Param(_, None) ->
          if not(L.mem not_bound_params p ~equal:equal_atom) then l1 @ [p], l2
          else l1, l2
        | Param(name, Some j) ->
          if L.mem free_indices j ~equal:equal_ivar then
            if not(L.mem not_bound_params p ~equal:equal_atom) then l1 @ [p], l2
            else l1, l2
          else
            if not(L.mem bound_params name ~equal:String.equal) && (L.length free_indices <= 5) then l1, l2 @ [p]
            else l1, l2 
        | _ -> assert false
      )
  |> (fun (l1,l2) -> l1 @ l2)
*)
(*
  L.fold_left sorted_params
   ~init:([],[])
   ~f:(fun (l1,l2) p ->
       let additional_list =
         if L.mem bound_params (atom_name p) ~equal:String.equal then []
         else
           match p with
           | Param(_, None) -> []
           | Param(name, Some _) -> [Param(name, Some i)]
           | _ -> assert false
       in
       if L.mem not_bound_params p ~equal:equal_atom then l1, l2 @ additional_list
       else l1 @ [p], l2 @ additional_list
      )
  |> (fun (l1,l2) -> l1 @ l2)*)

let split_in_factors_all (conj : conj) (depth : int) =
  let rec aux k previous = function
    | [] -> [conj]
    | c :: rest ->
      if c.constr_is_eq = InEq || c.constr_ivarsK <> []
      then aux (k+1) (previous @ [c]) rest
      else
        try
          let new_constrs = split_in_factors conj.conj_ivarsK c in
          if L.length new_constrs > 1 then
            let () = F.printf "%ssplit_in_factors %d.\n" (String.make depth ' ') k in
            L.map new_constrs ~f:(fun c -> mk_conj conj.conj_ivarsK (previous @ [c] @ rest))
          else
            aux (k+1) (previous @ [c]) rest
        with _ -> aux (k+1) (previous @ [c]) rest
  in
  aux 1 [] (conj.conj_constrs)

let simplify_coeffs_with_order (depth : int) (order : ivar list) (conj : conj) =
  let simp_sum (c : BI.t) (s : sum) =
    match s.sum_summand with
    | Mon(_) -> mk_poly [(c, s)]
    | Coeff(coeff) ->
      let handle_vars = handle_vars_list coeff.coeff_mon in
      begin match handle_vars with
        | [] -> mk_poly [(c, s)]
        | (Hvar h1) :: [] ->
          if (Set.exists (ivars_monom (umon2mon coeff.coeff_unif))
                 ~f:(fun j -> Util.before_in_list ~equal:equal_ivar h1.hv_ivar j order)) then
            let () = F.printf "%ssimplified_coeffs_with_index_order.\n" (String.make depth ' ') in
            SP.zero
          else
            mk_poly [(c, s)]
        | (Hvar h1) :: (Hvar h2) :: [] ->
          let ivars = ivars_monom (umon2mon coeff.coeff_unif) in
          if Set.exists ivars ~f:(fun j -> (before_in_list ~equal:equal_ivar h1.hv_ivar j order) &&
                                           (before_in_list ~equal:equal_ivar h2.hv_ivar j order))
          then
            let () = F.printf "%ssimplified_coeffs_with_index_order.\n" (String.make depth ' ') in
            SP.zero
          else
            mk_poly [(c, s)]
        | _ -> assert false
      end
  in
  let simp_poly (p : poly) =
    Map.fold p.poly_map
       ~init:SP.zero
       ~f:(fun ~key:s ~data:c p' ->
           SP.(p' +! (simp_sum c s))
         )
  in
  let simp_constr (c : constr) = mk_constr c.constr_ivarsK c.constr_is_eq (simp_poly c.constr_poly) in
  mk_conj conj.conj_ivarsK (L.map conj.conj_constrs ~f:simp_constr)

exception Found_contradiction

let rec simplify_if_possible (advK : advK) (depth : int) (n : int) (order : ivar list) (conj : conj) =
  match contradiction conj with
  | Some _ ->
    F.printf "%scontradiction.\n" (String.make depth ' ');
    raise Found_contradiction
  | None ->
    if n = 0 then conj
    else
      let new_conj = divide_by_not_null_params depth conj
                     |> divide_by_every_variable depth
                     |> simplify_coeffs_with_order depth order
                     |> simplify advK
      in
      if (equal_conj conj new_conj) then conj
      else
        let () = F.printf "%ssimplify.\n" (String.make depth ' ') in
        F.print_flush();
        simplify_if_possible advK depth (n-1) order new_conj

let is_single_param_poly (p : poly) =
  match Map.to_alist p.poly_map with
  | (s,_) :: [] ->
    begin match s.sum_summand with
      | Mon(mon)
        when L.length (params mon) = 1 && L.length (uvars mon) = 0 && L.length (hvars mon) = 0 ->
        let (param, degree) = L.hd_exn (params mon) in
        if BI.is_one degree then Some param
        else None
      | _ -> None
    end
  | _ -> None  

let update_used_params used_params conj =
  let rec aux used_free used_bound = function
    | [] -> used_free, used_bound
    | c :: rest ->
      match is_single_param_poly c.constr_poly with
      | None -> aux used_free used_bound rest
      | Some p ->
        begin match p with
          | Param(name, Some i) when L.mem (unzip1 c.constr_ivarsK) i ~equal:equal_ivar ->
            if L.mem used_bound name then aux used_free used_bound rest
            else aux used_free (name :: used_bound) rest
          | _ ->
            if L.mem used_free p ~equal:equal_atom then aux used_free used_bound rest
            else aux (p :: used_free) used_bound rest
        end
  in
  let used_free, used_bound = used_params in
  aux used_free used_bound conj.conj_constrs

let unfold_hvars conj unfolded_hvars lcombs =
  let unfold h used =
    let expression =
      match h.hv_gname, lcombs with
      | G1, (Some p, _) -> p
      | G2, (_, Some p) -> p
      | _ -> assert false
    in
    let old_parameters = Set.to_list (get_atoms_poly expression) |> L.filter ~f:is_param
                         |> L.map ~f:(fun p -> atom_name p) 
    in
    let new_params = Eval.fresh_params (L.length old_parameters) used in
    let rn = String.Map.of_alist_exn (L.zip_exn old_parameters new_params) in
    let new_sum s =
      match s.sum_summand with
      | Coeff(_) -> s
      | Mon(mon) ->
        let sum_atoms, sum_degrees = Map.to_alist mon.monom_map |> L.unzip in
        let new_atoms = L.map sum_atoms
            ~f:(function | Param(name, v) -> Param(Map.find_exn rn name, v) | a -> a)
        in
        let new_monom = mk_monom_of_map (Atom.Map.of_alist_exn (L.zip_exn new_atoms sum_degrees)) in
        let new_sum_ivarsK = match s.sum_ivarsK with
          | [] -> []
          | (i,iK) :: [] -> [i, Set.add iK h.hv_ivar]
          | _ -> assert false
        in
        mk_sum new_sum_ivarsK (Mon(new_monom))        
    in
    let renamed_expression =
      Map.fold expression.poly_map
        ~init:SP.zero
        ~f:(fun ~key:s ~data:c p' ->
            SP.(p' +! (mk_poly [(c, new_sum s)]))
          )
    in
    mk_constr [] Eq (SP.((of_atom (Hvar h)) -! renamed_expression))
  in
  let hvars = get_atoms_conj conj |> Set.filter ~f:is_hvar |> Set.to_list
              |> L.map ~f:(function | Hvar hv -> hv | _ -> assert false)
  in
  L.fold_left hvars
   ~init:(conj, unfolded_hvars)
   ~f:(fun (conj', unfolded') h ->
       if (L.mem unfolded' h ~equal:equal_hvar) || not(L.mem (unzip1 conj'.conj_ivarsK) h.hv_ivar ~equal:equal_ivar) then
         (conj', unfolded')
       else
         let parameters = Set.to_list (get_atoms_conj conj') |> L.filter ~f:is_param
                          |> L.map ~f:(fun p -> atom_name p)
         in
         (mk_conj conj'.conj_ivarsK (conj'.conj_constrs @ [unfold h parameters]), unfolded' @ [h])
      )

let unsolved_goals = ref 0

let rec automatic_algorithm (goals : proof_branch list) (advK : advK) (lcombs : poly option * poly option) =
  if (L.length goals) = 0 then !unsolved_goals = 0
  else if L.length goals > 100 then
    let current_branch = L.hd_exn goals in
    let () = F.printf "Current goal:\n%a\n" PPLatex.pp_conj_latex current_branch.branch_conj in
    false
  else
    let goals = dedup_preserve_order goals
        ~equal:(fun g1 g2 -> equal_conj g1.branch_conj g2.branch_conj)
    in
    let depth = (L.length goals) - 1 in
    let current_branch = L.hd_exn goals in
    (* let () = F.printf "%a\n" PPLatex.pp_conj_latex current_branch.branch_conj in *)

    let used_params = current_branch.branch_used_params in
    let ivars_order = current_branch.branch_free_ivars_order in
    let unfolded_hvars = current_branch.branch_unfolded_hvars in
    let only_if_simp = current_branch.branch_coeff_only_if_simp in
    let conj = current_branch.branch_conj in
    (* let conj, unfolded_hvars = unfold_hvars conj unfolded_hvars lcombs in *)
    try
      let conj = simplify_if_possible advK depth 2 ivars_order conj
                 |> introduce_coeff_everywhere depth advK only_if_simp
                 |> simplify_if_possible advK depth 2 ivars_order 
      in

      let used_params = update_used_params used_params conj in
      
      let disj' = split_in_factors_all conj depth in
      if (L.length disj' > 1) then
        let new_branches = L.map disj' ~f:(fun c -> mk_proof_branch c used_params ivars_order unfolded_hvars only_if_simp) in
        automatic_algorithm (new_branches @ (L.tl_exn goals)) advK lcombs
      else
        let disj' = assure_laurent_polys conj in
        if (disj' <> []) then
          let () = F.printf "%sassure_Laurent.\n" (String.make depth ' ') in
          let new_branches = L.map disj' ~f:(fun c -> mk_proof_branch c used_params ivars_order unfolded_hvars only_if_simp) in
          automatic_algorithm (new_branches @ (L.tl_exn goals)) advK lcombs
        else
          let parameters = parameters_to_split (mk_proof_branch conj used_params ivars_order unfolded_hvars only_if_simp) (unzip1 conj.conj_ivarsK) in
          let not_bound_params, bound_params = used_params in
          
          match L.hd parameters with
          | None ->
            if only_if_simp then
              let new_branch = mk_proof_branch conj used_params ivars_order unfolded_hvars false in
              automatic_algorithm (new_branch :: (L.tl_exn goals)) advK lcombs
            else
              let not_ordered_ivars = L.filter (unzip1 conj.conj_ivarsK)
                  ~f:(fun i -> not(L.mem ivars_order i ~equal:equal_ivar))
              in
              begin match not_ordered_ivars with
                | [] -> 
                  let conj = simplify_if_possible advK depth 5 ivars_order conj in
                  let () = F.printf "Current goal:\n%a\n" PPLatex.pp_conj_latex conj in
                  unsolved_goals := !unsolved_goals + 1;
                  automatic_algorithm (L.tl_exn goals) advK lcombs
                  (* false *)
                | i :: _ ->
                  let all_possible_orders = Util.insert i ivars_order in
                  let new_branches = L.map all_possible_orders
                      ~f:(fun o -> mk_proof_branch conj used_params o unfolded_hvars only_if_simp)
                  in
                  F.printf "%sadd_ivar_to_order %a\n" (String.make depth ' ') pp_ivar i;
                  automatic_algorithm (new_branches @ (L.tl_exn goals)) advK lcombs
              end

          | Some p ->
            F.printf "%scase_distinction %a.\n" (String.make depth ' ') pp_atom p;
            let cases, new_idx = case_distinction conj p in
            let second_list =
              match new_idx with
              | None -> bound_params
              | Some _ -> (atom_name p) :: bound_params
            in
            let branch1 =
              mk_proof_branch (L.nth_exn cases 0) (p :: not_bound_params, second_list) ivars_order unfolded_hvars only_if_simp
            in
            let branch2 =
              mk_proof_branch (L.nth_exn cases 1) (p :: not_bound_params, bound_params) ivars_order unfolded_hvars only_if_simp
            in
            automatic_algorithm ([branch1; branch2] @ (L.tl_exn goals)) advK lcombs
    with
    | Found_contradiction ->
      automatic_algorithm (L.tl_exn goals) advK lcombs
   
let automatic_prover cmds =
  let constraints, (k1,k2), lcombs = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let advK = Eval.adv_of_k1k2 (k1,k2) in
  let t1 = Unix.gettimeofday() in
  let proven =
    automatic_algorithm [mk_proof_branch constraints ([],[]) [] [] true] advK lcombs
  in
  let t2 = Unix.gettimeofday() in
  if proven then
    let () = F.printf "Proven!\nTime %F seconds\n" (t2 -. t1) in
    exit 0
  else
    let () = F.printf "There are %i unsolved goals\n" !unsolved_goals in
    let () = F.printf "Not proven!\nTime: %F seconds\n" (t2 -. t1) in
    exit 1    

let analyze_unbounded cmds instrs =
  let constraints, (k1,k2), _ = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let (system, nth) = Eval.eval_instrs (Wparse.p_instrs instrs) (k1,k2) [constraints] 1 in

  if (L.length system = 0) then
    F.printf "Proven!\n"
  else
    let constraints = L.nth_exn system (nth-1) in
    F.printf "Working on goal %d out of %d.\n" nth (L.length system);
    F.printf "%a" WconstrsUtil.pp_conj constraints;
    ()

let string_of_state st =
  let (system, nth) = st in
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  begin match system with
  | [] ->
    F.fprintf fbuf "<p>Proven!\n\n</p>"
  | _::_ ->
    let constraints = L.nth_exn system (nth-1) in
    F.fprintf fbuf
       "<p>Working on goal %d out of %d.</p>\n" nth (L.length system);
    F.fprintf fbuf "%a" PPLatex.pp_conj_latex constraints;
   ()
  end;
  F.pp_print_flush fbuf ();
  Buffer.contents buf
