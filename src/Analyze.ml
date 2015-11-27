open Core_kernel.Std
open Abbrevs
open Util
open Watom
open Wconstrs
open WconstrsUtil
open Wrules

let coeff_everywhere_constr (depth : int ) (c : constr) (n : int) (context : context_ivars) =
  let used_ivars = Set.union (Ivar.Set.of_list (unzip1 context)) (ivars_constr c) in
  let c_bound_ivars = Set.diff (ivars_constr c) (Ivar.Set.of_list (unzip1 context)) in
  let (rn,_) = renaming_away_from used_ivars c_bound_ivars in
  let ivars_context = (unzip1 context) in
  try
    match (L.filter (mons c.constr_poly) ~f:(fun m -> equal_monom m (uvars_monom m))) with
    | [] | _ :: [] -> []
    | monomials ->
      L.fold_left monomials
        ~init:[]
        ~f:(fun l m ->
            let m = map_idx_monom ~f:(apply_renaming rn) m in
            F.printf "%scoeff(%a) %d.\n" (String.make depth ' ') pp_monom m n; F.print_flush();
            let bound_ivars =
              Set.to_list (Set.filter (ivars_monom m) ~f:(fun i -> not(L.mem (ivars_context) i)))
            in
            let quant = Eval.maximal_quant ivars_context [] bound_ivars in
            l @ (introduce_coeff c quant (mon2umon m) context)
          )
  with _ -> []

let introduce_coeff_everywhere (depth : int) (conj : conj) =
  let rec aux new_constrs n = function
    | [] -> new_constrs
    | c :: rest ->
      if (c.constr_is_eq = Eq) then
        aux (new_constrs @ (coeff_everywhere_constr depth c n conj.conj_ivarsK)) (n+1) rest
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

let parameters_to_split (conj : conj) (used_params : atom list) =
  let i = { name = new_name (L.map (Set.to_list (ivars_conj conj)) ~f:(fun i -> i.name)); id = 0 } in
  let parameters = Set.to_list (get_atoms_conj conj) |> L.filter ~f:is_param in
  let frequencies = L.map parameters ~f:(fun p -> count_atom 0 p conj.conj_constrs) in
  let (_, sorted_params) = quicksort_double (>) frequencies parameters in
  L.fold_left sorted_params
   ~init:[]
   ~f:(fun l p ->
       if L.mem used_params p then
         match p with
         | Param(name, Some j) ->
           if L.mem (unzip1 conj.conj_ivarsK) j then l
           else [Param(name, Some i)] @ l
         | _ -> l
       else l @ [p]           
      )
  |> List.rev

let rec automatic_algorithm (depth : int) (used_params : atom list) (constrs : conj list) (advK : advK) =
  if constrs = [] then true
  else if L.length constrs > 50 then false
  else
    let conj = L.hd_exn constrs |> simplify advK in
    F.printf "%ssimplify.\n" (String.make depth ' ') ;
    match contradiction conj with
    | Some _ -> 
      F.printf "%scontradiction.\n" (String.make depth ' ');
      automatic_algorithm (depth-1) used_params (L.tl_exn constrs) advK
    | None -> 
      let conj = introduce_coeff_everywhere depth conj
                 |> simplify advK
                 |> (fun c -> let () = F.printf "%ssimplify.\n" (String.make depth ' ') in c)
                 |> divide_by_every_variable depth
                 |> divide_by_not_null_params depth
      in
      begin match contradiction conj with
        | Some _ ->
          F.printf "%scontradiction.\n" (String.make depth ' ');
          automatic_algorithm (depth-1) used_params (L.tl_exn constrs) advK
        | None ->
          let parameters = parameters_to_split conj used_params in
          match L.hd parameters with
          | None -> false
          | Some p ->
            F.printf "%scase_distinction %a.\n" (String.make depth ' ') pp_atom p;
            let cases = case_distinction conj p in
            automatic_algorithm (depth+1) (p :: used_params) (cases @ L.tl_exn constrs) advK
      end

let automatic_prover cmds =
  let constraints, (k1,k2) = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let advK = Eval.adv_of_k1k2 (k1,k2) in
  let t1 = Unix.gettimeofday() in
  let proven = automatic_algorithm 0 [] [constraints] advK in
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
