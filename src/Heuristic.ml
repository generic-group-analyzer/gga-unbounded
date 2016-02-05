(* ** Imports *)
open Core_kernel.Std
open Abbrevs
open Util
open Watom
open Wconstrs
open WconstrsUtil
open Wrules

(* ** Proof branch definition *)

type proof_branch = {
  branch_conj : conj;
  branch_used_params : atom list * string list;
  branch_ivars_order : ivar list;
  branch_unfolded_hvars : hvar list;
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

let mk_proof_branch conj used_params ivars_order unfolded_hvars =
  { branch_conj = conj; 
    branch_used_params = used_params;
    branch_ivars_order = ivars_order;
    branch_unfolded_hvars = unfolded_hvars;
  }

(* ** Get and sort parameters to split *)

let rec count_atom (counter : int) (p : atom) = function
  | [] -> counter
  | c :: rest ->
    if Set.mem (get_atoms_constr c) p then count_atom (counter+1) p rest
    else count_atom counter p rest

let parameters_to_split (branch : proof_branch) (free_indices : ivar list) =
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
            if not(L.mem bound_params name ~equal:String.equal) && (L.length free_indices <= 2) then l @ [p]
            else l
        | _ -> assert false
      )

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

(* ** Full simplification *)

exception Found_contradiction

let rec simplify_if_possible (advK : advK) (depth : int) (n : int) (order : ivar list) (conj : conj) =
  match contradiction conj with
  | Some _ ->
    F.printf "%scontradiction.\n" (String.make depth ' ');
    raise Found_contradiction
  | None ->
    if n = 0 then conj
    else
      let new_conj, msg_list1 = divide_by_not_null_params conj in
      let new_conj, msg_list2 = divide_by_every_variable new_conj in
      let new_conj = simplify_coeffs_with_order order new_conj
                     |> simplify advK
      in
      if (equal_conj conj new_conj) then conj
      else
        let () =
          print_messages depth msg_list1;
          print_messages depth msg_list2;
          F.printf "%ssimplify.\n" (String.make depth ' ');
          F.print_flush()
        in
        simplify_if_possible advK depth (n-1) order new_conj

(* ** Unfolding new Handle Variables *)

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

(* ** Automatic Algorithm *)

let rec automatic_algorithm (goals : proof_branch list) (advK : advK) (full_extraction : bool) (lcombs : poly option * poly option) =
  if (L.length goals) = 0 then true
  else if L.length goals > 100 then
    let current_branch = L.hd_exn goals in
    let () = F.printf "Current goal:\n%a\n" PPLatex.pp_conj_latex current_branch.branch_conj in
    false
  else
    let goals = dedup_preserve_order goals
        ~equal:(fun g1 g2 ->
            equal_conj g1.branch_conj g2.branch_conj &&
            g1.branch_ivars_order = g2.branch_ivars_order
          )
    in
    let depth = (L.length goals) - 1 in
    let current_branch = L.hd_exn goals in
    (* let () = F.printf "%a\n" PPLatex.pp_conj_latex current_branch.branch_conj in *)

    let used_params = current_branch.branch_used_params in
    let ivars_order = current_branch.branch_ivars_order in
    let unfolded_hvars = current_branch.branch_unfolded_hvars in
    let conj = current_branch.branch_conj in
    try
      let conj = simplify_if_possible advK depth 2 ivars_order conj in
      let conj, _msgs = introduce_coeff_everywhere advK full_extraction conj in
      F.printf "%sextract_coeffs.\n" (String.make depth ' ');
      F.print_flush();
      let conj = simplify_if_possible advK depth 2 ivars_order conj in

      let used_params = update_used_params used_params conj in
      
      let disj', msg = split_in_factors_all conj in
      print_messages depth msg;
      if (L.length disj' > 1) then
        let new_branches =
          L.map disj' ~f:(fun c -> mk_proof_branch c used_params ivars_order unfolded_hvars)
        in
        automatic_algorithm (new_branches @ (L.tl_exn goals)) advK full_extraction lcombs
      else
        let disj' = assure_laurent_polys conj in
        if (disj' <> []) then
          let () = F.printf "%sassure_Laurent.\n" (String.make depth ' ') in
          let new_branches =
            L.map disj' ~f:(fun c -> mk_proof_branch c used_params ivars_order unfolded_hvars)
          in
          automatic_algorithm (new_branches @ (L.tl_exn goals)) advK full_extraction lcombs
        else
          let parameters = parameters_to_split 
              (mk_proof_branch conj used_params ivars_order unfolded_hvars)
              (unzip1 conj.conj_ivarsK)
          in
          let not_bound_params, bound_params = used_params in
          
          match L.hd parameters with
          | None ->
            let not_ordered_ivars = L.filter (unzip1 conj.conj_ivarsK)
                ~f:(fun i -> not(L.mem ivars_order i ~equal:equal_ivar))
            in
            begin match not_ordered_ivars with
              | [] -> 
                let new_conj, unfolded_hvars = unfold_hvars conj unfolded_hvars lcombs in
                if (L.length new_conj.conj_constrs) = (L.length conj.conj_constrs) then
                  let conj = simplify_if_possible advK depth 5 ivars_order conj in
                  let () = F.printf "Current goal:\n%a\n" PPLatex.pp_conj_latex conj in
                  false
                else
                  let new_branch = mk_proof_branch new_conj used_params ivars_order unfolded_hvars in
                  automatic_algorithm (new_branch :: (L.tl_exn goals)) advK full_extraction lcombs
              | i :: _ ->
                let all_possible_orders = Util.insert i ivars_order in
                let new_branches = L.map all_possible_orders
                    ~f:(fun o -> mk_proof_branch conj used_params o unfolded_hvars)
                in
                F.printf "%sadd_ivar_to_order %a\n" (String.make depth ' ') pp_ivar i;
                automatic_algorithm (new_branches @ (L.tl_exn goals)) advK full_extraction lcombs
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
              mk_proof_branch (L.nth_exn cases 0) (p :: not_bound_params, second_list) ivars_order unfolded_hvars
            in
            let branch2 =
              mk_proof_branch (L.nth_exn cases 1) (p :: not_bound_params, bound_params) ivars_order unfolded_hvars
            in
            automatic_algorithm ([branch1; branch2] @ (L.tl_exn goals)) advK full_extraction lcombs
    with
    | Found_contradiction ->
      automatic_algorithm (L.tl_exn goals) advK full_extraction lcombs

let call_heuristic constraints advK lcombs =
  automatic_algorithm [mk_proof_branch constraints ([],[]) [] []] advK true lcombs
