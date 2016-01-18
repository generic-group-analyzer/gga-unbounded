open Core_kernel.Std
open Abbrevs
open Util
open Watom
open Wconstrs
open WconstrsUtil
open Wrules

let coeff_everywhere_constr (depth : int ) (c : constr) (n : int) (conj : conj) advK =
  let context = conj.conj_ivarsK in
  let used_ivars = Set.union (Ivar.Set.of_list (unzip1 context)) (ivars_constr c) in
  let c_bound_ivars = Set.diff (ivars_constr c) (Ivar.Set.of_list (unzip1 context)) in
  let (rn,_) = renaming_away_from used_ivars c_bound_ivars in
  let ivars_context = (unzip1 context) in
  try
    match L.filter (mons c.constr_poly) ~f:(fun m -> equal_monom m (uvars_monom m)) with
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
            let new_constrs = introduce_coeff c quant (mon2umon m) context in
            if L.exists ~f:(fun c -> L.mem conj.conj_constrs c ~equal:equal_constr)
                (L.map new_constrs ~f:(fun c -> simplify_coeff_constr c context advK)) then l
            else
              let () = F.printf "%scoeff(%a) %d.\n" (String.make depth ' ') pp_monom m n in
              F.print_flush();
              l @ new_constrs
          )
  with _ -> []

let introduce_coeff_everywhere (depth : int) (conj : conj) advK =
  let rec aux new_constrs n = function
    | [] -> new_constrs
    | c :: rest ->
      if (c.constr_is_eq = Eq) then
        aux (new_constrs @ (coeff_everywhere_constr depth c n conj advK)) (n+1) rest
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

let parameters_to_split (conj : conj) (used_params : atom list * string list) =
  let i = { name = new_name (L.map (Set.to_list (ivars_conj conj)) ~f:(fun i -> i.name)); id = 0 } in
   
  let parameters = Set.to_list (get_atoms_conj conj) |> L.filter ~f:is_param in
  let frequencies = L.map parameters ~f:(fun p -> count_atom 0 p conj.conj_constrs) in
  let (_, sorted_params) = quicksort_double (>) frequencies parameters in

  let not_bound_params, bound_params = used_params in

  L.fold_left sorted_params
   ~init:[]
   ~f:(fun l p ->
       let additional_list =
         if L.mem bound_params (atom_name p) then []
         else
           match p with
           | Param(_, None) -> []
           | Param(name, Some _) -> [Param(name, Some i)]
           | _ -> assert false
       in
       if L.mem not_bound_params p ~equal:equal_atom then l @ additional_list
       else l @ [p] @ additional_list
      )

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

let rec simplify_if_possible (advK : advK) (depth : int) (n : int) (conj : conj) =
  if n = 0 then conj
  else
    let new_conj = divide_by_not_null_params depth conj
                   |> divide_by_every_variable depth
                   |> simplify advK
    in
    if (equal_conj conj new_conj) then conj
    else
      let () = F.printf "%ssimplify.\n" (String.make depth ' ') in
      F.print_flush();
      simplify_if_possible advK depth (n-1) new_conj


let rec automatic_algorithm (used_params_global : (atom list * string list) list) (disjunction : conj list) (advK : advK) =
  if (L.length disjunction) = 0 then true
  else if L.length disjunction > 50 then
    let () = F.printf "Current goal:\n%a\n" PPLatex.pp_conj_latex (L.hd_exn disjunction) in
    false
  else
    let used_params_global, disjunction = 
      dedup_preserve_order ~equal:(fun (_,c1) (_,c2)-> equal_conj c1 c2)
        (L.zip_exn used_params_global disjunction)
      |> L.unzip
    in
    let depth = (L.length disjunction) - 1 in
    let used_params = L.hd_exn used_params_global in
(*    let () = F.printf "%a\n" pp_conj (L.hd_exn disjunction) in *)
    let conj = L.hd_exn disjunction in
    let conj = simplify_if_possible advK depth 2 conj in
    begin match contradiction conj with
    | Some _ -> 
      F.printf "%scontradiction.\n" (String.make depth ' ');
      automatic_algorithm (L.tl_exn used_params_global) (L.tl_exn disjunction) advK
    | None -> 
      let conj = introduce_coeff_everywhere depth conj advK
                 |> simplify_if_possible advK depth 2
      in
      begin match contradiction conj with
        | Some _ ->
          F.printf "%scontradiction.\n" (String.make depth ' ');
          automatic_algorithm (L.tl_exn used_params_global) (L.tl_exn disjunction) advK
        | None ->
          let disj' = split_in_factors_all conj depth in
          if (L.length disj' > 1) then
            automatic_algorithm 
              ((repeat_element used_params (L.length disj')) @ (L.tl_exn used_params_global))
              (disj' @ (L.tl_exn disjunction)) advK
          else
            let disj' = assure_laurent_polys conj in
            if (disj' <> []) then
              let () = F.printf "assure_Laurent.\n" in
              automatic_algorithm
                ((repeat_element used_params (L.length disj')) @ (L.tl_exn used_params_global))
                (disj' @ (L.tl_exn disjunction)) advK
            else
              let parameters = parameters_to_split conj used_params in
              let not_bound_params, bound_params = used_params in
  (*            F.printf "%a\n" pp_conj conj;
              F.printf "[%a]\n" (pp_list ", " pp_atom) not_bound_params;
              F.printf "[%a]\n" (pp_list ", " pp_string) bound_params;
              F.printf "[%a]\n" (pp_list ", " pp_atom) parameters;
              F.print_flush();*)
              match L.hd parameters with
              | None ->
                let conj = simplify_if_possible advK depth 5 conj in
                let () = F.printf "Current goal:\n%a\n" PPLatex.pp_conj_latex conj in
                false
              | Some p ->
                F.printf "%scase_distinction %a.\n" (String.make depth ' ') pp_atom p;
                let cases, new_idx = case_distinction conj p in
                let second_list =
                  match new_idx with
                  | None -> bound_params
                  | Some _ -> (atom_name p) :: bound_params
                in
                automatic_algorithm ([(p :: not_bound_params, second_list);
                                      (p :: not_bound_params, bound_params)] @
                                     (L.tl_exn used_params_global))
                  (cases @ L.tl_exn disjunction) advK
      end
    end

let automatic_prover cmds =
  let constraints, (k1,k2) = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let advK = Eval.adv_of_k1k2 (k1,k2) in
  let t1 = Unix.gettimeofday() in
  let proven = automatic_algorithm [[],[]] [constraints] advK in
  let t2 = Unix.gettimeofday() in
  if proven then
    let () = F.printf "Proven!\nTime %F seconds\n" (t2 -. t1) in
    exit 0
  else
    let () = F.printf "Not proven!\nTime: %F seconds\n" (t2 -. t1) in
    exit 1    

let analyze_unbounded cmds instrs =
  let constraints, (k1,k2) = Wparse.p_cmds cmds |> Eval.eval_cmds in
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
