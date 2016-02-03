(* * Constraint solving rules *)

(* ** Imports *)
open Core_kernel.Std
open Util
open Abbrevs
open Watom
open Wconstrs
open Sage
open Z3


(* ** Renaming: II *)

let rename_sum (s : sum) rn =
  if Set.is_empty (Set.inter (ivars_sum s) (Ivar.Set.of_list (Map.data rn))) then
    let ivars = L.map (unzip1 s.sum_ivarsK) ~f:(apply_renaming rn) in
    let isetsK = L.map (unzip2 s.sum_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn)) in
    let summand = map_idx_summand ~f:(apply_renaming rn) s.sum_summand in
    mk_sum (L.zip_exn ivars isetsK) summand
  else assert false

let rename_poly (p : poly) rn =
  if Set.is_empty (Set.inter (ivars_poly p) (Ivar.Set.of_list (Map.data rn))) then
    Map.fold p.poly_map
       ~init:SP.zero
       ~f:(fun ~key:s ~data:c p' -> SP.(p' +! (mk_poly [(c,rename_sum s rn)]) ) )
  else assert false

let rename_constr (c : constr) rn =
  if Set.is_empty (Set.inter (ivars_constr c) (Ivar.Set.of_list (Map.data rn))) then
    let qvars = L.map (unzip1 c.constr_ivarsK) ~f:(apply_renaming rn) in
    let qsetsK = L.map (unzip2 c.constr_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn)) in
    let poly = rename_poly c.constr_poly rn in
    mk_constr (L.zip_exn qvars qsetsK) c.constr_is_eq poly
  else assert false

let rename_conj (c : conj) rn =
  if Set.is_empty (Set.inter (ivars_conj c) (Ivar.Set.of_list (Map.data rn))) then
    let fvars = L.map (unzip1 c.conj_ivarsK) ~f:(apply_renaming rn) in
    let fsetsK = L.map (unzip2 c.conj_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn)) in
    let constrs = L.map c.conj_constrs ~f:(fun constr -> rename_constr constr rn) in
    mk_conj (L.zip_exn fvars fsetsK) constrs
  else assert false

(* ** "Split" rule *)
(* *** Substitute indices *)

let rename_sum_for_subst (s : sum) rn =
  let ivars = L.map (unzip1 s.sum_ivarsK) ~f:(apply_renaming rn) in
  let isetsK = L.map (unzip2 s.sum_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn)) in
  let summand = map_idx_summand ~f:(apply_renaming rn) s.sum_summand in
  mk_sum (L.zip_exn ivars isetsK) summand

let subst_idx_sum (s : sum) (i : ivar) (j : ivar) =
  let aux_sum = 
    if L.mem (unzip1 s.sum_ivarsK) j then
      let (rn,_) = renaming_away_from (ivars_sum s) (Ivar.Set.singleton j) in
      rename_sum_for_subst s rn
    else s
  in
  rename_sum_for_subst aux_sum (Ivar.Map.of_alist_exn [(i,j)])

let subst_idx_poly (p : poly) (i : ivar) (j : ivar) =
  Map.fold p.poly_map
     ~init:SP.zero
     ~f:(fun ~key:s ~data:c p -> SP.(p +! (mk_poly [(c, subst_idx_sum s i j)])))

let subst_idx_constr (c : constr) (i : ivar) (j : ivar) =
  let aux_constr =
    if L.mem (unzip1 c.constr_ivarsK) j then
      let (rn,_) = renaming_away_from (ivars_constr c) (Ivar.Set.singleton j) in
      let qvars = L.map (unzip1 c.constr_ivarsK) ~f:(apply_renaming rn) in
      let qsetsK = L.map (unzip2 c.constr_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn)) in
      let poly = subst_idx_poly c.constr_poly j (L.hd_exn (Map.data rn)) in
      mk_constr (L.zip_exn qvars qsetsK) c.constr_is_eq poly
    else c
  in
  let rn = Ivar.Map.of_alist_exn [(i,j)] in
  let qvars = L.map (unzip1 aux_constr.constr_ivarsK) ~f:(apply_renaming rn) in
  let qsetsK = L.map (unzip2 aux_constr.constr_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn)) in
  let poly = subst_idx_poly aux_constr.constr_poly i j in
  mk_constr (L.zip_exn qvars qsetsK) c.constr_is_eq poly
    
(* *** Ivars context *)

type context_ivars = (ivar * Ivar.Set.t) list with compare

let update_context context inner_context =
  let rec aux output = function
    | [] -> output
    | (i,iK) :: rest ->
      begin match L.find output ~f:(fun (i',_) -> equal_ivar i i') with
        | None -> aux (output @ [(i,iK)]) rest
        | Some _ -> aux ((L.filter output ~f:(fun (i',_) -> not (equal_ivar i i'))) @ [(i,iK)]) rest
      end
  in
  aux context inner_context

let context_distinct_ij i j context =
  match L.find context ~f:(fun (i',_) -> equal_ivar i i') with
  | None -> false
  | Some (_,iK) -> Set.mem iK j

let context_distinct i j context =
  (context_distinct_ij i j context) || (context_distinct_ij j i context)

(* *** Split ivar cases*)

let rec split_ivar_sum (s : sum) (i : ivar) (j : ivar) (context : context_ivars) =
  (* i is a summation-bound index and we split the sum into two parts if j is not in the exceptions *)
  if (equal_ivar i j) then assert false
  else
    match (L.find s.sum_ivarsK ~f:(fun (i',_) -> equal_ivar i i')) with
    | None -> failwith "i is not a summation-bound index variable"
    | Some (_, exceptions) ->
      if Set.exists exceptions ~f:(fun k -> not(context_distinct k j context)) then [s]
      else
        let first,_ = L.find_exn s.sum_ivarsK ~f:(fun (k,_) -> equal_ivar i k || equal_ivar j k) in
        if (equal_ivar first j) ||
           not (L.exists s.sum_ivarsK ~f:(fun (k,_) -> equal_ivar j k))
        then
          let ivarsK1 =
            L.map s.sum_ivarsK ~f:(fun (i',s') -> 
                if equal_ivar i i' then (i, Set.add s' j)
                else (i',s')
              )
          in
          let ivarsK2 =
            L.filter s.sum_ivarsK ~f:(fun (i',_) -> not (equal_ivar i i') && not (equal_ivar j i'))
          in
          let s1 = mk_sum ivarsK1 s.sum_summand in
          let s2 = subst_idx_sum (mk_sum ivarsK2 s.sum_summand) i j in
          let ivarsK2 =
            begin match L.find s.sum_ivarsK ~f:(fun (k,_) -> equal_ivar j k) with
              | None -> s2.sum_ivarsK
              | Some (j,jK) -> (j,jK) :: s2.sum_ivarsK
            end
          in
          [s1 ; mk_sum ivarsK2 s2.sum_summand]
        else
          split_ivar_sum s j i context
          
let rec split_ivar_constr (c : constr) (i : ivar) (j : ivar) (context : context_ivars) =
  (* i is a qbound index and we split the constraint into two cases if j is not in the exceptions *)
  if (equal_ivar i j) then assert false
  else  
    match (L.find c.constr_ivarsK ~f:(fun (i',_) -> equal_ivar i i')) with
    | None -> failwith "i is not a qbound index variable"
    | Some (_,exceptions) ->
      if Set.exists exceptions ~f:(fun k -> not(context_distinct k j context)) then [c]
      else
        let first,_ = L.find_exn c.constr_ivarsK ~f:(fun (k,_) -> equal_ivar i k || equal_ivar j k) in
        if (equal_ivar first i) ||
           not (L.exists c.constr_ivarsK ~f:(fun (k,_) -> equal_ivar j k))
        then
          let qvarsK1 =
            L.map c.constr_ivarsK ~f:(fun (i',s') ->
                if equal_ivar i i' then (i, Set.add s' j)
                else (i',s')
              )
          in
          let qvarsK2 = 
            L.filter c.constr_ivarsK ~f:(fun (i',_) -> not (equal_ivar i i') && not (equal_ivar j i'))
          in
          let c1 = mk_constr qvarsK1 c.constr_is_eq c.constr_poly in
          let c2 = subst_idx_constr (mk_constr qvarsK2 c.constr_is_eq c.constr_poly) i j in
          let qvarsK2 =
            begin match L.find c.constr_ivarsK ~f:(fun (k,_) -> equal_ivar j k) with
              | None -> c2.constr_ivarsK
              | Some (j,jK) -> (j,jK) :: c2.constr_ivarsK
            end
          in
          [ c1 ; mk_constr qvarsK2 c2.constr_is_eq c2.constr_poly]
        else
          split_ivar_constr c j i context

(* ** Adversary Knowledge *)

type advMsets = {
  sm_glob : umonom list;
  sm_orcl : umonom list;
  tm_glob : umonom list;
  tm_orcl : umonom list;
} with compare, sexp

type advK = {
  g1 : advMsets;
  g2 : advMsets;
}

let adv_sets advK = function
  | G1 -> advK.g1
  | G2 -> advK.g2

(* ** Make ivars distinct *)

let ivars_not_distinct (ivars : Ivar.Set.t) (context : context_ivars) =
  (* Returns a pair of ivars that are not defined to be distinct in the context *)
  let rec aux output = function
    | [] -> output
    | i :: rest ->
      let not_distinct = L.filter rest ~f:(fun j -> not (context_distinct i j context))
                         |> L.map ~f:(fun j -> (i,j))
      in
      aux (output @ not_distinct) rest
  in
  aux [] (Set.to_list ivars)

let all_ivars_distinct_sum (sum : sum) (context : context_ivars) =
  let rec aux s =
    let bound_ivars = unzip1 s.sum_ivarsK in
    let local_context = update_context context s.sum_ivarsK in
    let not_distinct  = ivars_not_distinct (Ivar.Set.of_list (unzip1 local_context)) local_context
                        |> L.filter ~f:(fun (i,j) ->
                            L.mem bound_ivars i || L.mem bound_ivars j)
    in
    let rec aux2 s = function
      | [] ->
        if L.length not_distinct > 0 then assert false
        else [s]
      | (i,j) :: rest ->
        let new_sums =
          if (L.mem bound_ivars i) then split_ivar_sum s i j local_context
          else if (L.mem bound_ivars j) then split_ivar_sum s j i local_context
          else assert false
        in
        if (L.length new_sums) = 1 then aux2 s rest
        else L.concat (L.map new_sums ~f:aux)
    in
    aux2 s not_distinct
  in
  aux sum

let all_ivars_distinct_poly (p : poly) (context : context_ivars) =
  Map.fold p.poly_map
     ~init:SP.zero
     ~f:(fun ~key:s ~data:c p' ->
         SP.(p' +! (mk_poly (L.map (all_ivars_distinct_sum s context) ~f:(fun s -> (c,s)) )))
       )

let all_ivars_distinct_constr (constr : constr) (context : context_ivars) =
  let rec aux c =
    let bound_ivars = unzip1 constr.constr_ivarsK in
    let local_context = update_context context c.constr_ivarsK in
    let not_distinct = ivars_not_distinct (Ivar.Set.of_list (unzip1 local_context)) local_context
                     |> L.filter ~f:(fun (i,j) -> L.mem bound_ivars i || L.mem bound_ivars j)
    in
    match not_distinct with
    | [] -> [mk_constr c.constr_ivarsK c.constr_is_eq (all_ivars_distinct_poly c.constr_poly local_context)]
    | (i,j) :: _ ->
      if (L.mem bound_ivars i) then L.concat (L.map (split_ivar_constr c i j local_context) ~f:aux)
      else if (L.mem bound_ivars j) then L.concat (L.map (split_ivar_constr c j i local_context) ~f:aux)
      else assert false
  in
  aux constr

let all_ivars_distinct_conj (conj : conj) =
  mk_conj conj.conj_ivarsK
    (L.concat (L.map conj.conj_constrs ~f:(fun c -> all_ivars_distinct_constr c conj.conj_ivarsK)))

(* ** "Coeff" rule *)
(* *** Introduce "Coeff" *)

type monlist = (atom * BI.t) list with compare

let equal_monlist a b =
  compare_monlist a b = 0

let monom_to_monlist p_var mon =
  Map.filter mon.monom_map ~f:(fun ~key:k ~data:_v -> p_var k)
  |> Map.to_alist
  |> L.sort ~cmp:(fun (k1,_) (k2,_) -> compare_atom k1 k2)

let expand_monom_list monom_list =
  (* Negative degree elements are omitted *)
  L.fold_left monom_list
   ~init:[]
   ~f:(fun l (k,v) -> l @ (repeat_element k (BI.to_int v)))

let uvars (mon : monom)  = monom_to_monlist is_uvar mon
let hvars (mon : monom)  = monom_to_monlist is_hvar mon
let params (mon : monom) = monom_to_monlist is_param mon

let uvars_monom  (mon : monom) = monom_filter_vars is_uvar mon
let hvars_monom  (mon : monom) = monom_filter_vars is_hvar mon
let params_monom (mon : monom) = monom_filter_vars is_param mon
let not_params_monom (mon : monom) = monom_filter_vars (fun v -> not(is_param v)) mon
let not_hvars_monom (mon : monom) = monom_filter_vars (fun v -> not(is_hvar v)) mon

let get_atoms_sum (s : sum) =
  match s.sum_summand with
  | Mon(mon) -> Atom.Set.of_list (unzip1 (Map.to_alist mon.monom_map))
  | Coeff(_) -> Atom.Set.empty 

let get_atoms_poly (p : poly) =
  Map.fold p.poly_map ~init:Atom.Set.empty ~f:(fun ~key:s ~data:_ se -> Set.union se (get_atoms_sum s))

let get_atoms_constr (c : constr) = get_atoms_poly c.constr_poly

let get_atoms_conj (c : conj) =
  L.fold_left c.conj_constrs ~init:Atom.Set.empty ~f:(fun s c -> Set.union s (get_atoms_constr c))

let handle_vars_list (mon : monom) =
  let rec aux output = function
    | [] -> output
    | (h,n) :: rest ->
      aux (output @ (repeat_element h (BI.to_int n))) rest
  in
  aux [] (hvars mon)

let contains_coeff_sum (s : sum) =
  match s.sum_summand with
  | Mon(_) -> false
  | Coeff(_) -> true

let contains_coeff_poly (p : poly) = L.exists (Map.keys p.poly_map) ~f:contains_coeff_sum

let contains_coeff_constr (c : constr) = contains_coeff_poly c.constr_poly

let introduce_coeff_sum (c : BI.t) (s : sum) (uM : umonom) (context : context_ivars) =
  let ivars_uM = ivars_umonom uM in
  let rec aux s =
    match s.sum_summand with
    | Mon(mon) ->
      begin match s.sum_ivarsK with
        | [] -> [mk_sum [] (Coeff(mk_coeff uM mon))]
        | (i,iK) :: rest_ivarsK ->
          begin match (Set.find ivars_uM
                          ~f:(fun j -> not(Set.exists iK 
                                              ~f:(fun k -> not(context_distinct k j context) )
                                          ) 
                             )
                      ) with
            | None -> 
              let sums = aux (mk_sum rest_ivarsK s.sum_summand) in
              L.map sums ~f:(fun s' -> mk_sum ((i,iK)::s'.sum_ivarsK) s'.sum_summand)
            | Some j ->
              let sums = split_ivar_sum s i j context in
              L.concat (L.map sums ~f:aux)
          end
      end
    | Coeff(coeff) ->
      if equal_monom (umon2mon coeff.coeff_unif) (mk_monom []) then [s]
      else []
  in
  L.fold_left (aux s)
   ~init:SP.zero
   ~f:(fun p s' -> SP.(p +! (mk_poly [(c, s')])))

let introduce_coeff_poly (p : poly) (uM : umonom) (context : context_ivars) =
  Map.fold p.poly_map
     ~init:SP.zero
     ~f:(fun ~key:s ~data:c p' -> SP.(p' +! introduce_coeff_sum c s uM context) )

let introduce_coeff (c : constr) (quant : (ivar * Ivar.Set.t) list) (uM : umonom) (context : context_ivars) =
  if (c.constr_is_eq = InEq) then failwith "impossible to introduce coeff in inequalities"
  else
    if Set.is_empty (Set.inter (Ivar.Set.of_list (unzip1 quant)) (ivars_constr c)) then
      let context' = update_context context (c.constr_ivarsK @ quant) in
      mk_constr (c.constr_ivarsK @ quant) Eq (introduce_coeff_poly c.constr_poly uM context')
      |> (fun c -> all_ivars_distinct_constr c [])
    else
      failwith "ivars intersection is not empty"

(* *** SMT solver *)

let degree (v : atom) (m : monom) =
  Option.value ~default:BI.zero (Map.find m.monom_map v)

let udegree (v : uvar) (m : umonom) =
  Option.value ~default:BI.zero (Map.find m.umonom_map v)

let smt_solver query =
  let result = call_z3 (query ^ "\n") in
  match result with
  | "true" -> true
  | "false" -> false
  | s -> failwith ("Communication with python failed, got <<" ^ s ^ ">>")

let create_matrix_vector vars uM uM_list =
  let rec aux matrix vector = function
    | [] -> matrix, vector
    | v :: rest ->
      let new_row = L.map uM_list ~f:(fun m -> udegree v m) in
      aux (matrix @ [new_row]) (vector @ [udegree v uM]) rest
  in
  aux [] [] vars

let vector2string vector = 
  let rec aux output = function
    | [] -> output
    | x :: [] -> output ^ (BI.to_string x)
    | x :: rest -> aux (output ^ (BI.to_string x) ^ ",") rest
  in
  (aux "[" vector) ^ "]"

let matrix2string matrix =
  let rec aux output = function
    | [] -> output
    | row :: [] -> output ^ (vector2string row)
    | row :: rest -> aux (output ^ (vector2string row) ^ ",") rest
  in
  (aux "[" matrix) ^ "]"

let satisfiable_system uM uM_list =
  let vars = L.concat (L.map (uM :: uM_list) ~f:(fun m -> Map.keys m.umonom_map))
             |> L.dedup ~compare:compare_uvar
  in
  let (matrix,vector) = create_matrix_vector vars uM uM_list in
  smt_solver ("{'matrix':" ^ (matrix2string matrix) ^ ",'vector':" ^ (vector2string vector) ^ "}")
  

(* *** Simplify "Coeff" *)

let rec canMult m advMsets forbidden_idxs =
  let rec aux j = function
    | [] -> false
    | m' :: rest ->
      let m' = mult_umonom m (inv_umonom (map_idx_umonom ~f:(fun _ -> j) m')) in
      if (canMult m' advMsets (forbidden_idxs @ [j])) then true
      else aux j rest
  in
  let ivarsM = ivars_umonom m in
  if Set.is_empty ivarsM then satisfiable_system m advMsets.tm_glob
  else
    if Set.is_empty (Set.inter ivarsM (Ivar.Set.of_list forbidden_idxs)) then
      let i = Set.choose_exn ivarsM in
      aux i advMsets.tm_orcl
    else false

let eval_contMon uM advMsets forbidden_idxs =
  let rec aux1 = function
    | [] -> false
    | m :: rest ->
      let m' = mult_umonom uM (inv_umonom m) in
      if (canMult m' advMsets forbidden_idxs) then true
      else aux1 rest
  in
  let rec aux2 j = function
    | [] -> false
    | m :: rest ->
      let m' = mult_umonom uM (inv_umonom (map_idx_umonom ~f:(fun _ -> j) m)) in
      if (canMult m' advMsets (forbidden_idxs @ [j])) then true
      else aux2 j rest
  in
  if (aux1 advMsets.sm_glob) then true
  else
    L.fold_left (Set.to_list (ivars_umonom uM))
     ~init:false
     ~f:(fun b j -> b || (if L.mem forbidden_idxs j ~equal:equal_ivar then false
                          else aux2 j advMsets.sm_orcl))

let cancelation_monomials advMsets1 advMsets2 =
  let f m = map_idx_umonom ~f:(fun _ -> { name = "fake"; id = 0 }) m in
  L.filter (cross_lists (L.map advMsets1.tm_orcl ~f) (L.map advMsets2.tm_orcl ~f)
           |> L.map ~f:(fun (m1,m2) -> mult_umonom m1 m2)
           )
   ~f:(fun m -> Set.is_empty (ivars_umonom m))

let satisfiable_system_double uM advMsets1 advMsets2 =
  satisfiable_system uM (advMsets1.tm_glob @ advMsets2.tm_glob @
                         cancelation_monomials advMsets1 advMsets2)

exception Not_simplifiable

type canMultObj = {
  monomial : umonom;
  sets1 : advMsets;
  sets2 : advMsets;
  forb1 : ivar list;
  forb2 : ivar list;
} with compare, sexp

module CanMultObj = struct
  module T = struct
    type t = canMultObj
    let compare = compare_canMultObj
    let sexp_of_t = sexp_of_canMultObj
    let t_of_sexp = canMultObj_of_sexp
  end
  include T
  include Comparable.Make(T)
end

let canMultTable = ref CanMultObj.Map.empty

let rec canMult_double m advMsets1 advMsets2 forb1 forb2 =
  let ivarsM = ivars_umonom m in
  if Set.is_empty ivarsM then satisfiable_system_double m advMsets1 advMsets2
  else
    if Set.is_empty (Set.inter ivarsM (Set.inter (Ivar.Set.of_list forb1) (Ivar.Set.of_list forb2)))
    then false
    else
      let obj = { monomial = m; sets1 = advMsets1; sets2 = advMsets2; forb1 = forb1; forb2 = forb2; } in
      match Map.find !canMultTable obj with
      | None -> 
        let try1 =
          L.fold_left (Set.to_list (Set.diff ivarsM (Ivar.Set.of_list forb1)))
           ~init:false
           ~f:(fun b j ->
               b || (L.exists (L.map advMsets1.tm_orcl
                                 ~f:(fun m' ->
                                     let m'' = mult_umonom m (inv_umonom m') in
                                     canMult_double m'' advMsets1 advMsets2 (j :: forb1) forb2))
                       ~f:(fun b -> b))
             )  
        in
        if try1 then
          let () = canMultTable := Map.add !canMultTable ~key:obj ~data:true in
          true
        else
          let try2 =
            L.fold_left (Set.to_list (Set.diff ivarsM (Ivar.Set.of_list forb2)))
              ~init:false
              ~f:(fun b j ->
                  b || (L.exists (L.map advMsets2.tm_orcl
                                    ~f:(fun m' ->
                                        let m'' = mult_umonom m (inv_umonom m') in
                                        canMult_double m'' advMsets1 advMsets2 forb1 (j :: forb2)))
                          ~f:(fun b -> b))
                )
          in
          let () = canMultTable := Map.add !canMultTable ~key:obj ~data:try2 in
          try2
      | Some answer -> answer

let combine_monoms advMsets forbidden_idxs ivars_uM =
  (L.map advMsets.sm_glob ~f:(fun m -> (m, forbidden_idxs) )) @
  L.fold_left ivars_uM
   ~init:[]
   ~f:(fun l j -> l @ (L.map advMsets.sm_orcl
                         ~f:(fun m -> (map_idx_umonom ~f:(fun _ -> j) m, j :: forbidden_idxs) )))

let eval_contMon_double uM advMsets1 advMsets2 forbidden_idxs1 forbidden_idxs2 =
  let ivars_uM = Set.to_list (ivars_umonom uM) in
  let monoms1 = combine_monoms advMsets1 forbidden_idxs1 ivars_uM in
  let monoms2 = combine_monoms advMsets2 forbidden_idxs2 ivars_uM in
  try
    let () = L.iter (cross_lists monoms1 monoms2)
        ~f:(fun ((m1, forb1) ,(m2, forb2)) ->
            let m' = mult_umonom (mult_umonom uM (inv_umonom m1)) (inv_umonom m2) in
            if canMult_double m' advMsets1 advMsets2 forb1 forb2 then raise Not_simplifiable
            else ()
          )
    in
    false
  with
  | Not_simplifiable -> true

let contMon coeff advK =
  let uM = mult_umonom coeff.coeff_unif (mon2umon (inv_monom (uvars_monom coeff.coeff_mon))) in
  let handle_vars = handle_vars_list coeff.coeff_mon in
  match handle_vars with
  | [] -> Map.is_empty uM.umonom_map
  | (Hvar h1) :: [] ->
    let advMsets = adv_sets advK h1.hv_gname in
    eval_contMon uM advMsets [h1.hv_ivar]
  | (Hvar h1) :: (Hvar h2) :: [] ->
    let advMsets1 = adv_sets advK h1.hv_gname in
    let advMsets2 = adv_sets advK h2.hv_gname in
    eval_contMon_double uM advMsets1 advMsets2 [h1.hv_ivar] [h2.hv_ivar]
  | _ -> assert false

let simplify_coeff_sum (c : BI.t) (s : sum) (context : context_ivars) (advK : advK) =
  let context = update_context context s.sum_ivarsK in
  match s.sum_summand with
  | Coeff(coeff) ->
    if (hvars coeff.coeff_mon) = [] && equal_umonom coeff.coeff_unif (mon2umon coeff.coeff_mon) then
      mk_poly [(c, mk_sum s.sum_ivarsK (Mon(params_monom coeff.coeff_mon)))]
    else
      if (contMon coeff advK) = false &&
         ivars_not_distinct (Set.union (ivars_umonom coeff.coeff_unif) (ivars_monom coeff.coeff_mon)) context = []
      then SP.zero
      else (* We cannot simplify it *)
        let uM = mult_umonom coeff.coeff_unif (mon2umon (inv_monom (uvars_monom coeff.coeff_mon))) in
        let m = mult_monom (hvars_monom coeff.coeff_mon) (params_monom coeff.coeff_mon) in
        mk_poly [(c, mk_sum s.sum_ivarsK (Coeff(mk_coeff uM m)))]
  | _ -> mk_poly [(c, s)]   (* It is already simplified *)

let simplify_coeff_poly (p : poly) (context : context_ivars) (advK : advK)=
  Map.fold p.poly_map
     ~init:SP.zero
     ~f:(fun ~key:s ~data:c p' -> SP.(p' +! (simplify_coeff_sum c s context advK) ))

let simplify_coeff_constr (c : constr) (context : context_ivars) (advK : advK) =
  mk_constr c.constr_ivarsK c.constr_is_eq (simplify_coeff_poly c.constr_poly (update_context context c.constr_ivarsK) advK)

let simplify_coeff_conj (advK : advK) (conj : conj) =
  let f c = simplify_coeff_constr c (conj.conj_ivarsK) advK in
  mk_conj conj.conj_ivarsK (L.map conj.conj_constrs ~f)


(* ** Groebner Basis *)
(* *** Opening *)

let normalize_ivarsK ivarsK name counter =
  let rec aux output n = function
    | [] -> Ivar.Map.of_alist_exn output, n
    | (i,_) :: rest -> aux (output @ [(i, {name = name; id = n})]) (n+1) rest
  in
  aux [] counter ivarsK

let normalize_ivars_sum (s : sum) (s_name : string) =
  if Set.exists (ivars_sum s) ~f:(fun i -> i.name = s_name) then assert false
  else
    let rn,_ = normalize_ivarsK s.sum_ivarsK s_name 1 in
    rename_sum s rn

let normalize_ivars_poly (p : poly) (s_name : string) =
  Map.fold p.poly_map
    ~init:SP.zero
    ~f:(fun ~key:s ~data:c p' ->
        SP.(p' +! (mk_poly [(c, normalize_ivars_sum s s_name)]))
      )

let normalize_ivars_constr (c : constr) (fa_name : string) (s_name : string) =
  if Set.exists (ivars_constr c) ~f:(fun i -> i.name = fa_name || i.name = s_name) then assert false
  else
    let rn,_ = normalize_ivarsK c.constr_ivarsK fa_name 1 in
    let c = rename_constr c rn in
    mk_constr c.constr_ivarsK c.constr_is_eq (normalize_ivars_poly c.constr_poly s_name)

let normalize_ivars (conj : conj) (ex_name : string) (fa_name : string) (s_name : string) =
  if Set.exists (ivars_conj conj) ~f:(fun i -> i.name = ex_name || i.name = fa_name || i.name = s_name)
  then assert false
  else
    let rn,_ = normalize_ivarsK conj.conj_ivarsK ex_name 1 in
    let conj = rename_conj conj rn in
    mk_conj conj.conj_ivarsK
      (L.map conj.conj_constrs ~f:(fun c -> normalize_ivars_constr c fa_name s_name))

let new_name names =
  let rec aux k =
    let name = "k'" ^ (Int.to_string k) in
    if (L.mem names name) then aux (k+1)
    else name
  in
  aux 1  

let normalize (conj : conj) =
  let names = ["i"; "j"; "k"] @ (L.map (Set.to_list (ivars_conj conj)) ~f:(fun i -> i.name)) in
  let ex_name = new_name names in
  let fa_name = new_name ([ex_name] @ names) in
  let s_name  = new_name ([ex_name; fa_name] @ names) in
  let conj = normalize_ivars conj ex_name fa_name s_name in
  normalize_ivars conj "i" "j" "k"

let opening (conj : conj) =
  let conj = normalize conj in
  conj

let closing (conj : conj) =
  let conj = normalize conj in
  let new_constrs = dedup_preserve_order ~equal:equal_constr conj.conj_constrs in
  mk_conj conj.conj_ivarsK new_constrs  

let maximal_excp_sets_sum (s : sum) (context : context_ivars) =
  let context = update_context context s.sum_ivarsK in
  (ivars_not_distinct (Ivar.Set.of_list (unzip1 s.sum_ivarsK)) context) = []

let maximal_excp_sets_constr (c : constr) (context : context_ivars) =
  let context = update_context context c.constr_ivarsK in
  (ivars_not_distinct (Ivar.Set.of_list (unzip1 c.constr_ivarsK)) context) = [] &&
  (Map.fold c.constr_poly.poly_map
      ~init:true
      ~f:(fun ~key:s ~data:_ b -> 
          b && (maximal_excp_sets_sum s (update_context context context))
        )
  )

let maximal_exception_sets (conj : conj) =
  (ivars_not_distinct (Ivar.Set.of_list (unzip1 conj.conj_ivarsK)) conj.conj_ivarsK) = [] &&
  not (L.exists conj.conj_constrs ~f:(fun c -> not (maximal_excp_sets_constr c conj.conj_ivarsK) ))

(* *** Abstraction *)

type abstract =
  | Sigma of sum
  | P of param
  with compare, sexp

type abstraction = { abstracts : abstract list } with compare

let mk_abstraction (abstracts : abstract list) =
  let is_sum_one = function
    | Sigma(s) -> equal_sum s (mk_sum [] (Mon(mk_monom [])))
    | _ -> false
  in
  let prefered_order a1 a2 =
    match a1, a2 with
    | Sigma(s1), Sigma(s2) -> (L.length s2.sum_ivarsK) - (L.length s1.sum_ivarsK)
    | Sigma(_), P(_) -> -1
    | P(_), Sigma(_) ->  1
    | P(p1), P(p2) -> (Set.length (ivars_atom (Param p2))) - (Set.length (ivars_atom (Param p1)))
  in
  let abstracts = L.dedup abstracts ~compare:compare_abstract
                  |> L.filter ~f:(fun a -> not(is_sum_one a))
  in
  let abstracts = L.sort ~cmp:prefered_order (L.sort ~cmp:compare_abstract abstracts) in
  { abstracts = abstracts }

let pp_abstract = function
  | Sigma(s) -> F.printf "%a " PPLatex.pp_sum_latex s
  | P(p) -> F.printf "%a " PPLatex.pp_param_latex p

let pp_abstraction abs =
  L.iter abs.abstracts ~f:(fun a -> let () = pp_abstract a in F.print_flush())

let extract_abstracts_sum (s : sum) =
  let f ~key:a ~data:_  =
    begin match a with
      | Param(_, None) -> false
      | Param(_, Some i) -> L.mem ~equal:equal_ivar (unzip1 s.sum_ivarsK) i
      | _ -> true
    end
  in
  let new_summand, summand_monom =
    match s.sum_summand with
    | Mon(mon) -> Mon(mk_monom_of_map (Map.filter mon.monom_map ~f)), mon
    | Coeff(c) -> 
      let coeff = mk_coeff c.coeff_unif (mk_monom_of_map (Map.filter c.coeff_mon.monom_map ~f)) in
      Coeff(coeff), c.coeff_mon
  in
  let sigma = mk_sum s.sum_ivarsK new_summand in
  let not_bound =
    Map.filter summand_monom.monom_map ~f:(fun ~key:a ~data:_d -> not (f ~key:a ~data:_d))
    |> Map.to_alist
    |> L.map ~f:(function | (Param(p), d) -> (P(p),d) | _ -> assert false)
  in
  if equal_sum sigma (mk_sum [] (Mon(mk_monom []))) && L.length not_bound > 0 then not_bound
  else (Sigma(sigma), BI.one) :: not_bound

let abstraction_from_parampolys (parampolys : poly list) =
  let extract_abstracts_poly (p : poly) =
    Map.fold p.poly_map
       ~init:[]
       ~f:(fun ~key:s ~data:_ l -> l @ (unzip1 (extract_abstracts_sum s)))
  in
  L.fold_left parampolys
   ~init:[]
   ~f:(fun l p -> l @ (extract_abstracts_poly p))
  |> mk_abstraction

(* *** Groebner polynomials *)

type gb_poly = (BI.t * BI.t list) list

let abs_sum2degrees (s : sum) (abs : abstraction) =
  let abstracts_from_sum = extract_abstracts_sum s in
  let rec aux output = function
    | [] -> output
    | ab :: rest ->
      begin match L.find abstracts_from_sum ~f:(fun (a,_) -> compare_abstract a ab = 0) with
        | None -> aux (output @ [BI.zero]) rest
        | Some (_,d) -> aux (output @ [d]) rest
      end
  in
  aux [] abs.abstracts

exception Not_Valid_Sum_Degree

let abs_degrees2sum (degrees : BI.t list) (abs : abstraction) =
  let sums = L.map (L.zip_exn abs.abstracts degrees)
      ~f:(function
          | Sigma(s), d ->
            if (BI.is_one d) then [s]
            else if (BI.is_zero d) then []
            else if (BI.equal d (BI.of_int 2)) then [ mult_sum s s ]
            else raise Not_Valid_Sum_Degree
          | P(p), d ->
            if (BI.is_zero d) then []
            else [mk_sum [] (Mon(mk_monom_of_map (Atom.Map.of_alist_exn [(Param(p), d)] )))]
        )
        |> L.concat
  in
  L.fold_left sums
   ~init:(mk_sum [] (Mon(mk_monom [])))
   ~f:(fun s s' -> mult_sum s s')

let poly2gb_poly (p : poly) (abs : abstraction) =
  Map.fold p.poly_map
     ~init:[]
     ~f:(fun ~key:s ~data:c l -> l @ [(c, abs_sum2degrees s abs)])
(*
let gb_poly2poly (gbp : gb_poly) (abs : abstraction) =
  L.fold_left gbp
   ~init:SP.zero
   ~f:(fun p (c,l) -> SP.(p +! (mk_poly [(c, abs_degrees2sum l abs)])) )
*)
let string_of_gb_poly (gbp : gb_poly) =
  let rec aux output = function
    | [] -> output
    | (c,l) :: []   ->      output ^ "(" ^ (BI.to_string c) ^ "," ^ (vector2string l) ^ ")"
    | (c,l) :: rest -> aux (output ^ "(" ^ (BI.to_string c) ^ "," ^ (vector2string l) ^ "),") rest
  in
  "[" ^ (aux "" gbp) ^ "]"

let poly_of_gb_string (s : string) (abs : abstraction) =
  let terms = String.split s ~on:'t' in
  let terms_list =
    L.map terms ~f:(fun t ->
        let coeffs = String.split t ~on:',' in
        let coeffs = L.map coeffs ~f:(Big_int.big_int_of_string) in
        (L.hd_exn coeffs, L.tl_exn coeffs)
      )
  in
  L.fold_left terms_list
   ~init:SP.zero
   ~f:(fun p (c,degrees) -> SP.(p +! (mk_poly [(c, abs_degrees2sum degrees abs)])) )

let poly_system_of_gb_string (s : string) (abs : abstraction) =
  if s = "" then []
  else
    let polynomials = String.split s ~on:'p' in
    L.map polynomials ~f:(fun s' -> try poly_of_gb_string s' abs with     
                                      | Not_Valid_Sum_Degree -> SP.zero
                                      | Mult_of_Coeffs -> SP.zero
                                      | _ -> assert false
                         )

let param_poly_equation (c : constr) =
  let is_param_sum (s : sum) =
    match s.sum_summand with
    | Coeff(_) -> s.sum_ivarsK = [] && c.constr_ivarsK = []
    | Mon(mon) -> equal_monom (params_monom mon) mon
  in
  c.constr_is_eq = Eq &&
  (Map.fold c.constr_poly.poly_map
     ~init:true
     ~f:(fun ~key:s ~data:_ b -> b && (is_param_sum s) )
  )

let without_variables_but_possibly_coeffs (c : constr) =
  let is_valid_sum (s : sum) =
    match s.sum_summand with
    | Coeff(_) -> true
    | Mon(mon) -> equal_monom (params_monom mon) mon
  in
  c.constr_is_eq = Eq &&
  (Map.fold c.constr_poly.poly_map
     ~init:true
     ~f:(fun ~key:s ~data:_ b -> b && (is_valid_sum s) )
  )

let without_summations (c : constr) =
  Map.fold c.constr_poly.poly_map
     ~init:true
     ~f:(fun ~key:s ~data:_ b -> b && (s.sum_ivarsK = []))

(* *** x-poly *)

(* A x-poly is a list of tupples (xterms) where each of them corresponds to a sum quantification. *)

type xterm = {
  xterm_ivarsK : (ivar * Ivar.Set.t) list;
  xterm_param_poly : poly;
  xterm_summand : summand;
} with compare, sexp

(* xterm_param_poly is supposed to not contain Uvars, Hvars and Summations. *)

type xpoly = { xpoly_list : xterm list }

let xsplit (s : sum) =
  match s.sum_summand with
  | Mon(mon) -> (params_monom mon, Mon(not_params_monom mon) )
  | Coeff(coeff) ->
    let new_coeff = mk_coeff coeff.coeff_unif (not_params_monom coeff.coeff_mon) in
    (params_monom coeff.coeff_mon, Coeff(new_coeff))

let rec equal_ivarsK ivarsK1 ivarsK2 =
  match ivarsK1, ivarsK2 with
  | [],[] -> true
  | (i,iK) :: rest_i, (j,jK) :: rest_j ->
    if equal_ivar i j && Set.equal iK jK then equal_ivarsK rest_i rest_j
    else false
  | _ -> false

let xpoly_of_poly (p : poly) =
  let rec aux xterms = function
    | [] -> xterms
    | (s,c) :: rest ->
      let (xparams, xsummand) = xsplit s in
      let f x =
        (equal_ivarsK x.xterm_ivarsK s.sum_ivarsK) &&
        (equal_summand x.xterm_summand xsummand)
      in
      let new_xterms = L.filter xterms ~f:(fun x -> not (f x)) in
      match L.find xterms ~f with
      | None ->
        aux (xterms @
             [{xterm_ivarsK = s.sum_ivarsK;
               xterm_param_poly = mk_poly [(c, mk_sum [] (Mon(xparams)))];
               xterm_summand = xsummand;
              }]) rest
      | Some x ->
        aux (new_xterms @
             [{xterm_ivarsK = x.xterm_ivarsK;
               xterm_param_poly = SP.(x.xterm_param_poly +! (mk_poly [(c, mk_sum [] (Mon(xparams)))]));
               xterm_summand = x.xterm_summand;
              }]) rest
  in
  aux [] (Map.to_alist p.poly_map)

let poly_of_xterm (x : xterm) =
  Map.fold x.xterm_param_poly.poly_map
     ~init:SP.zero
     ~f:(fun ~key:s ~data:c p ->
         if s.sum_ivarsK <> [] then assert false
         else
           let new_summand =
             match x.xterm_summand with
             | Mon(mon) ->  mult_summand (Mon(mon)) s.sum_summand
             | Coeff(coeff) ->
               begin match s.sum_summand with
                 | Mon(m) -> Coeff(mk_coeff coeff.coeff_unif (mult_monom m coeff.coeff_mon))
                 | _ -> raise Mult_Coeff_by_Var
               end
           in
           SP.(p +! (mk_poly [(c, mk_sum x.xterm_ivarsK new_summand)]))
     )

let poly_of_xpoly (xp : xpoly) (xp_aux : xpoly) =
  L.fold_left (L.zip_exn xp.xpoly_list xp_aux.xpoly_list)
   ~init:SP.zero
   ~f:(fun p (x, xaux) ->
      try SP.(p +! (poly_of_xterm x)) with
        | Mult_Coeff_by_Var -> SP.(p +! (poly_of_xterm xaux))
        | Mult_of_Coeffs    -> SP.(p +! (poly_of_xterm xaux))
        | _ -> assert false
     )

(* *** Groebner basis solving *)

let rec gb_system_of_gb_polys output = function
  | [] -> output
  | gp :: [] ->                          output ^ (string_of_gb_poly gp)
  | gp :: rest -> gb_system_of_gb_polys (output ^ (string_of_gb_poly gp) ^ ",") rest

let groebner_basis (param_polys : poly list) (abs : abstraction) =
  let param_polys = L.filter param_polys ~f:(fun p -> not (equal_poly p SP.zero)) in
  let gb_polys = L.map param_polys ~f:(fun p -> poly2gb_poly p abs) in
  let gb_system = "[" ^ (gb_system_of_gb_polys "" gb_polys) ^ "]" in
  let () = Out_channel.write_all "ubt.log" ~data:("{'cmd':'GroebnerBasis','system':" ^ gb_system ^ "}\n") in
  let groebner_basis = call_Sage ("{'cmd':'GroebnerBasis','system':" ^ gb_system ^ "}\n") in
  poly_system_of_gb_string groebner_basis abs

let gb_reduce (param_polys : poly list) (poly_to_reduce : poly) (abs : abstraction) =
  let param_polys = L.filter param_polys ~f:(fun p -> not (equal_poly p SP.zero)) in
  let gb_polys = L.map param_polys ~f:(fun p -> poly2gb_poly p abs) in
  let gb_system = "[" ^ (gb_system_of_gb_polys "" gb_polys) ^ "]" in
  let gb_poly_to_reduce = poly2gb_poly poly_to_reduce abs in
  let reduced =
    call_Sage ("{'cmd':'reduce','system':" ^ gb_system ^
               ",'to_reduce':" ^ (string_of_gb_poly gb_poly_to_reduce) ^ "}\n")
  in
  if reduced = "" then poly_to_reduce
  else poly_of_gb_string reduced abs

let permute_param_polys ivars polys =
  let ivars = L.dedup ivars ~compare:compare_ivar in
  let ivars_polys =
    L.fold_left polys
     ~init:Ivar.Set.empty
     ~f:(fun s p -> Set.union s (ivars_poly p))
    |> Set.to_list
  in      
  let not_used_name = new_name (L.map (ivars @ ivars_polys) ~f:(fun i -> i.name)) in
  let aux_ivars = L.map (range 1 (L.length ivars)) ~f:(fun n -> { name = not_used_name; id = n }) in
  let aux_rn = Ivar.Map.of_alist_exn (L.zip_exn ivars aux_ivars) in
  let aux_polys = L.map polys ~f:(fun p -> rename_poly p aux_rn) in
  let rec aux output = function
    | [] -> output
    | perm :: rest_perms ->
      let rn = Ivar.Map.of_alist_exn (L.zip_exn aux_ivars perm) in
      aux (output @ (L.map aux_polys ~f:(fun p -> rename_poly p rn))) rest_perms
  in
  aux [] (perms ivars)

let groebner_basis_simplification (conj : conj) =
  if maximal_exception_sets conj then
    let conj = opening conj in
    let delta_binder =
      L.fold_left conj.conj_constrs
       ~init:[]
       ~f:(fun l c ->
           if (L.length c.constr_ivarsK) <= (L.length l) then l
           else c.constr_ivarsK
         )
    in
    (* Phase 1: GB computation*)
    let param_polys = L.filter conj.conj_constrs ~f:param_poly_equation
                      |> L.map ~f:(fun c -> c.constr_poly)
                      |> permute_param_polys (unzip1 delta_binder)
                      |> L.dedup ~compare:compare_poly
    in
    let rest_constrs = L.filter conj.conj_constrs ~f:(fun c -> not (param_poly_equation c)) in
    let abs = abstraction_from_parampolys param_polys in
    let param_polys = groebner_basis param_polys abs in
    let new_constrs =
      rest_constrs @
      (L.map param_polys ~f:(fun p ->
          let ivars_p = ivars_poly p in
          let ivars_d = Ivar.Set.of_list (unzip1 delta_binder) in
          let binder = L.map delta_binder
              ~f:(fun (i,iK) -> (i, Set.filter iK 
                                   ~f:(fun j -> Set.mem ivars_p j ||
                                                not (Set.mem ivars_d j)
                                      )
                                )
                 )
          in
          mk_constr binder Eq p)
      |> L.map ~f:(fun c -> all_ivars_distinct_constr c conj.conj_ivarsK)
      |> L.concat
      )
    in
    (* Phase 2: Simplification below binders *)
    let param_poly_constrs_without_sums =
      L.filter new_constrs ~f:(fun c -> (without_variables_but_possibly_coeffs c) && (without_summations c))
    in
    let rest_constraints =
      L.filter new_constrs ~f:(fun c -> not(without_variables_but_possibly_coeffs c) || not(without_summations c))
    in
    let simplified_rest =
      L.map rest_constraints
       ~f:(fun c ->
            let () = if (maximal_excp_sets_constr c []) then () else assert false in
            let xpoly = xpoly_of_poly c.constr_poly in
            L.map xpoly
             ~f:(fun x ->
               let x_ivars = c.constr_ivarsK @ x.xterm_ivarsK in
               let n = L.length c.constr_ivarsK in
               if (L.length delta_binder) > (L.length x_ivars) then
                 let rn =
                   if (L.length x.xterm_ivarsK) > 0 then
                     Ivar.Map.of_alist_exn
                       (L.zip_exn
                          (L.slice (unzip1 delta_binder) n (n+(L.length x.xterm_ivarsK)))
                          (unzip1 x.xterm_ivarsK) 
                       )
                   else
                     Ivar.Map.empty
                 in
                 let param_polys =
                   L.map (L.map ~f:(fun c -> c.constr_poly) param_poly_constrs_without_sums)
                    ~f:(fun p -> rename_poly p rn)
                   |> permute_param_polys
                     ((L.dedup ~compare:compare_ivar (unzip1 x_ivars)) @
                      (L.slice (unzip1 delta_binder) (L.length x_ivars) (L.length delta_binder)))
                   |> L.dedup ~compare:compare_poly
                 in
                 let abs = abstraction_from_parampolys (x.xterm_param_poly :: param_polys) in
                 let reduced = gb_reduce param_polys x.xterm_param_poly abs in
                 { x with xterm_param_poly = reduced }, x
               else
                 let param_polys = L.map ~f:(fun c -> c.constr_poly) param_poly_constrs_without_sums in
                 let ivars_polys =
                   L.fold_left param_polys
                     ~init:Ivar.Set.empty
                     ~f:(fun s p -> Set.union s (ivars_poly p))
                   |> Set.to_list
                 in      
                 let not_used_name = new_name (L.map ((unzip1 delta_binder) @ ivars_polys) ~f:(fun i -> i.name)) in
                 let aux_ivars =
                   L.map (range 1 ((L.length x_ivars)-(L.length delta_binder)))
                     ~f:(fun n -> { name = not_used_name; id = n })
                 in
                 let rn = 
                   Ivar.Map.of_alist_exn
                     (L.zip_exn
                        ((L.slice (unzip1 delta_binder) n (L.length delta_binder)) @ aux_ivars)
                        (unzip1 x.xterm_ivarsK)
                     )
                 in
                 let param_polys = L.map param_polys ~f:(fun p -> rename_poly p rn)
                                   |> permute_param_polys (L.dedup ~compare:compare_ivar (unzip1 x_ivars))
                                   |> L.dedup ~compare:compare_poly
                 in
                 let abs = abstraction_from_parampolys (x.xterm_param_poly :: param_polys) in
                 let reduced = gb_reduce param_polys x.xterm_param_poly abs in
                 { x with xterm_param_poly = reduced }, x
             )

            |> (fun list -> mk_constr delta_binder c.constr_is_eq
                   (poly_of_xpoly { xpoly_list = (unzip1 list) } { xpoly_list  = (unzip2 list) } ))
          )
    in
    mk_conj conj.conj_ivarsK (simplified_rest @ param_poly_constrs_without_sums)
    |> closing
  else
    failwith "exception sets are not maximal"

(* ** Dividing rule *)

let divide_monom_by (a : atom) (m : monom) =
  Map.change m.monom_map a
    (function
      | None -> failwith "atom does not appear in the monomial"
      | Some i -> if BI.is_one i then None else Some (BI.(i -! one))
    )
  |> mk_monom_of_map

let divide_sum_by (a : atom) (s : sum) =
  match s.sum_summand with
  | Mon(mon) -> mk_sum s.sum_ivarsK (Mon(divide_monom_by a mon))
  | Coeff(coeff)->
    begin match a with
      | Param(_,_) ->
        let new_coeff = mk_coeff coeff.coeff_unif (divide_monom_by a coeff.coeff_mon) in
        mk_sum s.sum_ivarsK (Coeff(new_coeff))
      | _ -> failwith "division of Coeff by variable not allowed"
    end

let divide_poly_by (a : atom) (p : poly) =
  if equal_poly SP.zero p then p, false
  else
    try Map.fold p.poly_map
          ~init:SP.zero
          ~f:(fun ~key:s ~data:c p' -> SP.(p' +! (mk_poly [(c, divide_sum_by a s)]))), true
    with _ -> p, false

let divide_constr_by (a : atom) (constr : constr) =
  let new_poly, divided = divide_poly_by a constr.constr_poly in
  (mk_constr constr.constr_ivarsK constr.constr_is_eq new_poly), divided

let divide_conj_by (a : atom) (conj : conj) =
  match L.find (conj.conj_constrs)
          ~f:(fun c -> equal_constr c (mk_constr [] InEq (SP.of_atom a)) ||
                       equal_constr c (mk_constr [] InEq SP.(opp (of_atom a)))) with
  | None ->
    begin match a with
      | Uvar(_,_) ->
        let (new_constrs, divided) = L.unzip (L.map conj.conj_constrs ~f:(divide_constr_by a)) in
        (mk_conj conj.conj_ivarsK new_constrs, L.exists divided ~f:(fun b -> b))
      | _ -> failwith "atom might be null, division is not allowed"
    end
  | Some c ->
    let (new_constrs, divided) = L.unzip (L.map conj.conj_constrs ~f:(divide_constr_by a)) in
    mk_conj conj.conj_ivarsK (new_constrs @ [c]), L.count divided ~f:(fun b -> b) > 1

(* ** Simplify *)

let clear_trivial (conj : conj) =
  let f (c : constr) =
    not (
      ((equal_poly c.constr_poly SP.zero) && (c.constr_is_eq = Eq))   ||
      ((equal_poly c.constr_poly SP.one)  && (c.constr_is_eq = InEq))
    )
  in
  mk_conj conj.conj_ivarsK (L.filter conj.conj_constrs ~f)

let matching_sums (i1,s1) (i2,s2) =
  if (L.length i1) < (L.length i2) then false
  else
    let ivars1 = (unzip1 i1) @ (unzip1 s1.sum_ivarsK) in
    let ivars2 = (unzip1 i2) @ (unzip1 s2.sum_ivarsK) in
    if (L.length ivars1) <> (L.length ivars2) then false
    else
      let j = new_name (L.map (ivars1 @ ivars2) ~f:(fun x -> x.name)) in
      let aux_ivars = L.map (range 1 (L.length ivars1)) ~f:(fun n -> { name = j; id = n }) in
      let rn1 = Ivar.Map.of_alist_exn (L.zip_exn ivars1 aux_ivars) in
      let rn2 = Ivar.Map.of_alist_exn (L.zip_exn aux_ivars ivars2) in
      let aux_sum1 = mk_sum (i1 @ s1.sum_ivarsK) s1.sum_summand in
      let aux_sum2 = mk_sum (i2 @ s2.sum_ivarsK) s2.sum_summand in
      let aux_sum1 = rename_sum aux_sum1 rn1 in
      let aux_sum1 = rename_sum aux_sum1 rn2 in
      equal_sum aux_sum1 aux_sum2

let simplify_sums (c : constr) (to_simplify : constr) =
  if c.constr_is_eq = InEq then to_simplify
  else
    match Map.to_alist c.constr_poly.poly_map with
    | (s,_) :: [] ->
      let new_poly = 
        Map.fold to_simplify.constr_poly.poly_map
           ~init:SP.zero
           ~f:(fun ~key:s' ~data:c' p' ->
               if (matching_sums (c.constr_ivarsK, s) (to_simplify.constr_ivarsK, s')) then p'
               else SP.(p' +! (mk_poly [(c',s')]))
             )
      in
      mk_constr to_simplify.constr_ivarsK to_simplify.constr_is_eq new_poly
    | _ -> to_simplify

let simplify_constr_with_constr (c : constr) (to_simplify : constr) =
  let to_simplify = simplify_sums c to_simplify in
  if c.constr_is_eq = InEq || not(equal_ivarsK c.constr_ivarsK to_simplify.constr_ivarsK) then
    to_simplify
  else
    let n_summands = L.length (Map.to_alist to_simplify.constr_poly.poly_map) in
    let new_poly = SP.(to_simplify.constr_poly +! c.constr_poly) in
    if (L.length (Map.to_alist new_poly.poly_map) < n_summands) then
      mk_constr to_simplify.constr_ivarsK to_simplify.constr_is_eq new_poly
    else
      let new_poly = SP.(to_simplify.constr_poly -! c.constr_poly) in
      if (L.length (Map.to_alist new_poly.poly_map) < n_summands) then
        mk_constr to_simplify.constr_ivarsK to_simplify.constr_is_eq new_poly
      else to_simplify    

let simplify_eqs_in_others (conj : conj) =
  let rec f previous = function
    | [] -> previous
    | c :: next ->
      f ((L.map previous ~f:(simplify_constr_with_constr c)) @ [c])
        (L.map next ~f:(simplify_constr_with_constr c))
  in         
  mk_conj conj.conj_ivarsK (f [] conj.conj_constrs)

let remove_independent_equations (conj : conj) =
  (* We say an equation is independent if it has a parameter that only occurs in it *)
  (* FIXME : To be less incomplete, only remove things when the parameter degree is one *)
  let p_occurs_in_constrs constrs p =
    L.fold_left constrs
     ~init:false
     ~f:(fun b c ->
         let params = get_atoms_constr c |> Set.filter ~f:is_param in
         b || (L.exists (Set.to_list params) ~f:(fun p' -> (atom_name p') = (atom_name p)) )
       )
  in
  let rec aux new_constrs = function
    | [] -> new_constrs
    | c :: rest ->
      let vars = get_atoms_constr c |> Set.filter ~f:(fun p -> not (is_param p)) in
      let params = get_atoms_constr c |> Set.filter ~f:is_param in
      if Set.exists params ~f:(fun p -> not (p_occurs_in_constrs (new_constrs @ rest) p) ) &&
         Set.is_empty vars
      then aux new_constrs rest
      else aux (new_constrs @ [c]) rest
  in
  mk_conj conj.conj_ivarsK (aux [] conj.conj_constrs)

let uniform_vars_constr (context : context_ivars) (c : constr) =
  let rec aux c = function
    | [] -> c
    | v :: rest ->
      let min_degree =
        Map.fold c.constr_poly.poly_map
           ~init:[]
           ~f:(fun ~key:s ~data:_ l ->
               let d' = degree v (match s.sum_summand with Mon(mon) -> mon | _ -> assert false) in
               d' :: l
             )
        |> L.min_elt ~cmp:BI.compare
        |> (function | None -> assert false | Some d -> d)
      in
      if (BI.compare min_degree BI.zero) = 0 then aux c rest
      else
        let m = mk_monom_of_map (Atom.Map.of_alist_exn [(v, BI.opp min_degree)]) in
        let new_poly =
          Map.fold c.constr_poly.poly_map
             ~init:SP.zero
             ~f:(fun ~key:s ~data:c p ->
                 match s.sum_summand with
                 | Mon(mon) -> SP.(p +! (mk_poly [(c, mk_sum s.sum_ivarsK (Mon(mult_monom m mon)))]))
                 | _ -> assert false
               )
        in
        aux (mk_constr c.constr_ivarsK c.constr_is_eq new_poly) rest
  in
  try
    let uvars_c = Set.filter (Set.filter (get_atoms_constr c) ~f:is_uvar)
        ~f:(fun u -> match u with 
            | Uvar(_, None) -> true
            | Uvar(_, Some i) -> L.mem ~equal:equal_ivar (unzip1 (c.constr_ivarsK @ context)) i
            | _ -> assert false
          )
    in
    aux c (Set.to_list uvars_c)
  with _ -> c

let uniform_vars (conj : conj) =
  mk_conj conj.conj_ivarsK (L.map conj.conj_constrs ~f:(uniform_vars_constr conj.conj_ivarsK))

let simplify_null_handle_var_sum hvar c s = 
  match s.sum_summand with
  | Mon(mon) ->
    let hvars_to_compare, _ = hvars mon |> L.unzip in
    if (L.mem hvars_to_compare hvar ~equal:equal_atom) then []
    else [(c,s)]
  | Coeff(coeff) ->
    let hvars_to_compare, _ = hvars coeff.coeff_mon |> L.unzip in
    if (L.mem hvars_to_compare hvar ~equal:equal_atom) then []
    else [(c,s)]

let simplify_null_handle_var_constr hvar c =
  mk_constr c.constr_ivarsK c.constr_is_eq
    (Map.fold c.constr_poly.poly_map
        ~init:SP.zero
        ~f:(fun ~key:s ~data:c p'->
            SP.(p' +! (mk_poly (simplify_null_handle_var_sum hvar c s)))
          )
    )

let simplify_null_handle_vars (conj : conj) =
  let rec aux output = function
    | [] -> output
    | c :: rest ->
      if (c.constr_is_eq = Eq) then
        begin match Map.to_alist c.constr_poly.poly_map with
        | (s,_c) :: [] ->
          begin match s.sum_summand with
            | Mon(mon) when s.sum_ivarsK = [] ->
              begin match Map.to_alist mon.monom_map with
                | (Hvar(hv),_d) :: [] ->
                  aux (L.map output ~f:(fun c -> simplify_null_handle_var_constr (Hvar(hv)) c )) rest
                | _ -> aux output rest
              end
            | _ -> aux output rest
          end
        | _ -> aux output rest
        end
      else aux output rest
  in
  mk_conj conj.conj_ivarsK (aux conj.conj_constrs conj.conj_constrs)

let total_degree (m : monom) =
  Map.fold m.monom_map
     ~init:BI.zero
     ~f:(fun ~key:_a ~data:d td -> BI.(td +! d))

let remove_complex_equations (conj : conj) =
  let not_complex_sum (s : sum) =
    match s.sum_summand with
    | Coeff(_) -> true
    | Mon(mon) ->
      if equal_monom (params_monom mon) mon then BI.compare (total_degree mon) (BI.of_int 3) <= 0
      else true
  in
  let not_complex_constr (c : constr) =
    (* We need inequalities to derive contradictions, so we keep them all *)
    if c.constr_is_eq = InEq then true
    else
      Map.fold c.constr_poly.poly_map
         ~init:true
         ~f:(fun ~key:s ~data:_ b -> b && (not_complex_sum s))
  in
  mk_conj conj.conj_ivarsK (L.filter conj.conj_constrs ~f:not_complex_constr)


let simplify (advK : advK) (conj : conj) =
  clear_trivial conj
  |> simplify_coeff_conj advK
  |> opening
  |> all_ivars_distinct_conj
  |> groebner_basis_simplification
  |> simplify_eqs_in_others
  |> uniform_vars
  |> simplify_null_handle_vars
  |> remove_complex_equations (* we are still sound after removing some equations *)
(*  |> remove_independent_equations*)
  |> clear_trivial

(* ** Old functions FIXME *)
(* The previous Eval.ml needs these functions, we will get rid of them soon *)

let mons (p : poly) =
  Map.fold p.poly_map
    ~init:[]
    ~f:(fun ~key:s ~data:_c list ->
      let mon = match s.sum_summand with | Mon(m) -> m | Coeff(_) -> mk_monom [] in
      (Map.filter mon.monom_map ~f:(fun ~key:v ~data:_e -> not (is_param v))) :: list)
  |> L.map ~f:mk_monom_of_map
  |> L.dedup ~compare:compare_monom

(* Adversary knowledge data type *)

type k_inf = {
  non_recur : monom list  ; (* non-recursive knowledge in G_i *)
  recur     : monom list  ; (* recursive knowledge in G_i *)
  recur_idx : monom list  ; (* recursive indexed knowledge in G_i *)
}

let power_poly (p : poly) (e : BI.t) =
  let rec aux p' n = if BI.is_one n then p' else aux SP.(p' *! p) BI.(n -! one) in
  if BI.(compare e zero) < 0 then failwith "Not supported"
  else if BI.(compare e zero) = 0 then SP.one else aux p e


(* ** Laurent polynomials rule *)
(* This rule adds conditions on the parameters to make the handle variables be Laurent
   polynomials (and not rational functions) *)

let sum2string (s : sum) (variables : atom list) (sums : sum list) =
  match s.sum_summand with
  | Mon(mon) ->
    let (l, new_monom) =
      L.fold_left variables
       ~init:([], mon.monom_map)
       ~f:(fun (l,m) v -> 
           l @ [BI.to_string (degree v mon)], Map.remove m v
         )
    in
    l @
    (L.fold_left sums
       ~init:[]
       ~f:(fun l s' ->
           if equal_sum s' (mk_sum s.sum_ivarsK (Mon(mk_monom_of_map new_monom))) then l @ ["1"]
           else l @ ["0"]
         )
    )
    |> stringlist2string
  | _ -> assert false

let poly2string (p : poly) (variables : atom list) (sums : sum list) =
  Map.fold p.poly_map
    ~init:[]
    ~f:(fun ~key:s ~data:c output ->
        output @ ["(" ^ (BI.to_string c) ^ ",[" ^ (sum2string s variables sums) ^ "])"]
      )
  |> stringlist2string

let degrees2sum (degrees : BI.t list) (variables : atom list) (sums : sum list) =
  let rec aux mon vars degs = 
    match vars, degs with
    | [],[] -> mon
    | v :: rest_vars, d :: rest_degs ->
      if (BI.is_zero d) then aux mon rest_vars rest_degs
      else aux (mult_monom_atom mon (d,v)) rest_vars rest_degs
    | _ -> assert false
  in
  let rec aux2 s sums degs =
    match sums, degs with
    | [],[] -> s
    | s' :: rest_sums, d :: rest_degs ->
      if (BI.is_zero d) then aux2 s rest_sums rest_degs
      else if (BI.is_one d) then aux2 (mult_sum s s') rest_sums rest_degs
      else assert false
    | _ -> assert false
  in
  let degrees_vars = L.sub degrees ~pos:0 ~len:(L.length variables) in
  let degrees_sums = L.sub degrees ~pos:(L.length variables) ~len:(L.length sums) in
  let s = aux2 (mk_sum [] (Mon(mk_monom []))) sums degrees_sums in
  mult_sum s ( mk_sum [] (Mon(aux (mk_monom []) variables degrees_vars)) )

let string2poly (s : string) (variables : atom list) (sums : sum list) =
  L.map (String.split s ~on:'t')
    ~f:(fun t -> 
        let coeffs = String.split t ~on:','
                     |> L.map ~f:Big_int.big_int_of_string
        in
        (L.hd_exn coeffs, L.tl_exn coeffs)
      )
  |> L.fold_left
    ~init:SP.zero
    ~f:(fun p (c,degrees) -> SP.(p +! (mk_poly [(c, degrees2sum degrees variables sums)])))

let laurent_polys_rule (c : constr) (h : atom) (f : poly) (g : poly) =
  (* f and g have no summations and not handle variables *)
  let atoms = Set.union (get_atoms_poly f) (get_atoms_poly g) |> Set.to_list in
  let parameters = L.filter atoms ~f:is_param in
  let unif_vars  = L.filter atoms ~f:is_uvar in
  let variables = parameters @ unif_vars in
  (call_Sage
     ("{'cmd':'Laurent','f':[" ^ (poly2string f variables []) ^ "],'g':[" ^ (poly2string g variables []) ^ 
      "],'nparams':" ^ (string_of_int (L.length parameters)) ^ "}\n")
   |> (fun string ->
          if string = "" then [] else
            L.map (String.split string ~on:'|') ~f:(fun l -> L.map (String.split l ~on:'p')
                 ~f:(fun p_string -> mk_constr c.constr_ivarsK Eq (string2poly p_string variables []) ))
          )
  )
  @
  [
    [mk_constr c.constr_ivarsK Eq f; mk_constr c.constr_ivarsK Eq g];
    [mk_constr c.constr_ivarsK Eq f; mk_constr c.constr_ivarsK Eq (SP.of_atom h)];
  ]
  
let assure_laurent_polys (conj : conj) =
  let f_constr (c : constr) =
    match Set.to_list (get_atoms_poly c.constr_poly |> Set.filter ~f:is_hvar), c.constr_is_eq with
    | [], _ -> None
    | h :: [], Eq ->
      begin try
        Some
          (h, Map.fold c.constr_poly.poly_map
                 ~init:(SP.zero, SP.zero)
                 ~f:(fun ~key:s ~data:c (f,g) ->
                     begin match s.sum_summand, s.sum_ivarsK with
                       | Mon(mon), [] ->
                         begin match hvars mon with
                           | [] -> (SP.(f +! (mk_poly [(c,s)])), g)
                           | (h2, d) :: [] ->
                             if (equal_atom h h2) && (BI.equal d BI.one) then
                               (f, SP.(g +! (mk_poly[(c, mk_sum [] (Mon(not_hvars_monom mon)))])))
                             else assert false
                           | _ -> assert false
                         end
                       | _ -> assert false
                     end
                   )
          )
        with | _ -> None
      end
    | _ -> None
  in
  let rec aux previous = function
    | [] -> []
    | c :: rest ->
      match f_constr c with
      | None -> aux (previous @ [c]) rest
      | Some (h,(f,g)) -> (* h*g-f = 0 *)
        if (equal_poly f SP.zero) then
          let c1 = mk_constr c.constr_ivarsK Eq (SP.of_atom h) in
          let c2 = mk_constr c.constr_ivarsK Eq g in
          [mk_conj conj.conj_ivarsK (previous @ rest @ [c1]);
           mk_conj conj.conj_ivarsK (previous @ rest @ [c2])]
        else
          L.map (laurent_polys_rule c h f g)
            ~f:(fun l -> mk_conj conj.conj_ivarsK (conj.conj_constrs @ l))
  in
  aux [] conj.conj_constrs

(* ** Zero-product property *)

let raw_sum s =
  match s.sum_summand with
  | Mon(mon) ->
    let new_monom = Map.filter mon.monom_map
        ~f:(fun ~key:a ~data:_-> not (Set.is_empty (Set.inter (ivars_atom a)
                                                  (Ivar.Set.of_list (unzip1 s.sum_ivarsK)))))
    in
    mk_sum s.sum_ivarsK (Mon(mk_monom_of_map new_monom))
  | _ -> assert false

let get_raw_sums (p : poly) =
  Map.fold p.poly_map
     ~init:Sum.Set.empty
     ~f:(fun ~key:s ~data:_ set ->
         if s.sum_ivarsK = [] then set
         else Set.add set (raw_sum s)
       )

let split_in_factors (context : context_ivars) (c : constr) =
  if c.constr_is_eq = InEq then failwith "Impossible to split in factors an inequality"
  else if c.constr_ivarsK <> [] then failwith "Impossible to split in factors under a forall binder"
  else
    let sum_is_coeff = function | Coeff(_) -> true | _ -> false in
    match Map.to_alist c.constr_poly.poly_map with
    | (s,constant) :: [] when (sum_is_coeff s.sum_summand) && s.sum_ivarsK = [] ->
      begin match s.sum_summand with
      | Coeff(coeff) ->
        if (params coeff.coeff_mon = []) then [c]
        else
          let s1 = mk_sum [] (Coeff(mk_coeff coeff.coeff_unif (hvars_monom coeff.coeff_mon))) in
          let s2 = mk_sum [] (Mon(params_monom coeff.coeff_mon)) in
          [ mk_constr [] Eq (mk_poly [(constant,s1)]);
            mk_constr [] Eq (mk_poly [(constant,s2)]) ]
      | _ -> assert false
      end
    | _ ->
      let context = update_context context c.constr_ivarsK in
      let atoms = Set.to_list (get_atoms_poly c.constr_poly)
                  |> L.filter ~f:(fun a ->
                      match a with
                      | Uvar(_, Some i) | Param(_, Some i) ->
                        L.mem ~equal:equal_ivar (unzip1 context) i
                      | Uvar(_, None) | Param(_, None) -> true
                      | Hvar hv -> L.mem ~equal:equal_ivar (unzip1 context) hv.hv_ivar
                    )
      in
      begin try
          let sums = Set.to_list (get_raw_sums c.constr_poly) in
          call_Sage ("{'cmd':'factor','f':[" ^ (poly2string c.constr_poly atoms sums) ^ "]}\n")
          |> String.split ~on:'p'
          |> L.map ~f:(fun p_string -> mk_constr c.constr_ivarsK Eq (string2poly p_string atoms sums))
        with _ -> failwith "Equation contains Summations or Coeff"
      end

(* ** Case distinctions *)

let case_distinction (conj : conj) (p : atom) =
  match p with
  | Param (_, None) ->
     let c1 = mk_constr [] Eq   (SP.of_atom p) in
     let c2 = mk_constr [] InEq (SP.of_atom p) in
     L.map [c1; c2] ~f:(fun c -> mk_conj conj.conj_ivarsK (conj.conj_constrs @ [c]) ), None
       
  | Param (name, Some i) ->
    if (L.mem ~equal:equal_ivar (unzip1 conj.conj_ivarsK) i) then
      let c1 = mk_constr [] Eq   (SP.of_atom p) in
      let c2 = mk_constr [] InEq (SP.of_atom p) in
      L.map [c1; c2] ~f:(fun c -> mk_conj conj.conj_ivarsK (conj.conj_constrs @ [c]) ), None
    else
      let iE = Ivar.Set.of_list (unzip1 conj.conj_ivarsK) in
      let c1 = mk_constr [(i,iE)] Eq (SP.of_atom p) in
      let j_name = new_name (L.map (Set.to_list (ivars_conj conj)) ~f:(fun x -> x.name)) in
      let j = { name = j_name; id = 0 } in  (* j is a fresh index variable *)
      let c2 = mk_constr [] InEq (SP.of_atom (Param(name, Some j))) in
      [ mk_conj  conj.conj_ivarsK             (conj.conj_constrs @ [c1]);
        mk_conj (conj.conj_ivarsK @ [(j,iE)]) (conj.conj_constrs @ [c2])
        |> normalize
      ], Some j
  | _ -> failwith "parameter expected"

(* ** Contradictions *)

let is_not_null_constant (p : poly) =
  match Map.to_alist p.poly_map with
  | (s,c) :: [] ->
    (s.sum_ivarsK = []) && (equal_summand s.sum_summand (Mon(mk_monom []))) && not (BI.is_zero c)
  | _ -> false

let contradiction (conj : conj) =
  let f (c : constr) =
    (equal_poly c.constr_poly SP.zero   && c.constr_is_eq = InEq) ||
    (is_not_null_constant c.constr_poly && c.constr_is_eq = Eq)
  in
  L.find (conj.conj_constrs) ~f
