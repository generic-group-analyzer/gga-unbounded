(* * Winning constraint utility functions *)

(* ** Imports *)
open Wconstrs
open Watom
open Abbrevs
open Util
open Core_kernel.Std

(* ** Isomorphic constraints
 * ----------------------------------------------------------------------- *)

let matching_term (c1,s1) (c2,s2) ren =
  let free1 = L.filter (Set.to_list (free_ivars_sum s1)) ~f:(fun x -> (Ivar.Map.find ren x)=None) in
  let free2 = L.filter (Set.to_list (free_ivars_sum s2)) ~f:(fun x -> (Ivar.Map.find ren x)=None) in
  let bound1 = s1.ivars in
  let bound2 = s2.ivars in
  if (BI.compare c1 c2 <> 0) ||
     (L.length free1 <> L.length free2) || (L.length bound1 <> L.length bound2) then []
  else
    let f_perms = perms free1 in
    let b_perms = perms bound1 in

    let rec aux output f_list b_list =
    match f_list with
      | [] -> output
      | f::rest_f ->
        begin match b_list with
        | [] -> aux output rest_f b_perms
        | b::rest_b ->
          let rn = Ivar.Map.of_alist_exn (L.zip_exn (f @ b) (free2 @ bound2)) in
          if equal_sum (rename_sum s1 rn) s2 then
            let new_rn = Ivar.Map.of_alist_exn ((Map.to_alist ren) @ (L.zip_exn f free2)) in
            aux (new_rn :: output) rest_f rest_b
          else
            aux output f_list rest_b
        end
    in
    aux [] f_perms b_perms

let invert_rn rn =
  let (k,v) = L.unzip (Map.to_alist rn) in
  Ivar.Map.of_alist_exn (L.zip_exn v k)

let matching_poly (p1 : poly) (p2 : poly) =
  let p1 = p1.poly_map in
  let p2 = p2.poly_map in
  let rec aux xs ys ren =
    match xs with
    | [] -> [ren]
    | (s1,c1)::rest_xs ->
       let renamings = L.map ys ~f:(fun (s2,c2) -> matching_term (c1,s1) (c2,s2) ren) in
       let ys_residues = rm_diagonal ys in
       let rename_terms terms rn = L.map terms ~f:(fun (s,c) -> (rename_sum s (invert_rn rn), c)) in
       let residues =
         L.map2_exn renamings ys_residues
           ~f:(fun rns terms -> L.map rns ~f:(rename_terms terms)) in
       L.map2_exn (L.concat renamings) (L.concat residues)
        ~f:(fun rn ys_rest -> aux rest_xs ys_rest rn)
       |> L.concat
  in
  if (Map.length p1) <> (Map.length p2) then []
  else aux (Map.to_alist p1) (Map.to_alist p2) (Ivar.Map.empty)

let matching_constr c1 c2 = (* This does not check the q_ineq *)
  let valid_rn rn =
    let (ivars1, ivars2) = L.unzip (Map.to_alist rn) in
    L.map2_exn ivars1 ivars2
     ~f:(fun i j ->
          ((L.mem ~equal:equal_ivar c1.qvars i) && (L.mem ~equal:equal_ivar c2.qvars j)) ||
          (not ((L.mem ~equal:equal_ivar c1.qvars i)
                || (L.mem ~equal:equal_ivar c2.qvars j)))
          && (equal_ivar i j))
    |> L.fold_left ~init:true ~f:(&&)
  in
  L.filter (matching_poly c1.poly c2.poly) ~f:(valid_rn)

let isomorphic_sum s1 s2 = L.length (matching_term (BI.one,s1) (BI.one,s2) Ivar.Map.empty) > 0

let isomorphic_constr c1 c2 =
  equal_is_eq c1.is_eq c2.is_eq &&
  (L.length (matching_constr c1 c2) > 0 ||
   L.length (matching_constr c1 (fixme "{ c2 with poly = SP.opp c2.poly }")) > 0)

let isomorphic_poly p1 p2 =
  L.length (matching_constr (mk_constr [] [] Eq p1) (mk_constr [] [] Eq p2)) > 0

(* ** Distinct IVars
 * ----------------------------------------------------------------------- *)

(*
let all_pairs (ivars : ivar list) =
  L.filter (L.cartesian_product ivars ivars) ~f:(fun (x,y) -> x <> y)
  |> L.dedup ~compare:Ivar_Pair.compare

let all_ivar_distinct membership update_t rename ivars_t t =
  let rec do_split x = function
    | [] -> [x]
    | (i,j) :: rest_pairs ->
       if membership x (i,j) then do_split x rest_pairs
       else
         let ts1 = do_split (update_t x (i,j)) rest_pairs in
         let ts2 = do_split (rename x i j) (all_pairs (ivars_t (rename x i j))) in
         ts1 @ ts2
  in
  do_split t (all_pairs (ivars_t t))

let all_ivar_distinct_poly p =
  let membership s (i,j) = Set.mem (Ivar_Pair.Set.of_list s.i_ineq) (i,j) in
  let update s pair = mk_sum s.ivars (pair::s.i_ineq) s.monom in
  let rename s i j =
    let f x = if x = i then j else x in
    mk_sum
      (L.map s.ivars ~f)
      (L.map s.i_ineq ~f:(fun (x,y) -> (f x, f y)))
      (map_idx_monom s.monom ~f)
  in
  let ivars_t s = s.ivars in
  Map.fold p
    ~init:Sum.Map.empty
    ~f:(fun ~key:s ~data:c p' ->
          L.fold_left
            (L.map
               (all_ivar_distinct membership update rename ivars_t s)
               ~f:(fun x -> (c,x)))
        ~init:p'
          ~f:add_poly_term)
*)

(*
let all_ivar_distinct_constr_conj conj =
  let membership c (i,j) = L.mem c.q_ineq (i,j) in
  let update c pair = mk_constr c.qvars (pair::c.q_ineq) c.is_eq c.poly in
  let rename c i j =
    let f = (fun x -> if x = i then j else x) in
    mk_constr (L.map c.qvars ~f) (L.map c.q_ineq ~f:(fun (x,y) -> (f x, f y)))
      c.is_eq (map_idx_poly ~f c.poly)
  in
  let ivars_t c = c.qvars in
  L.map conj ~f:(all_ivar_distinct membership update rename ivars_t)
  |> L.concat
*)

(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

let is_eq_to_string = function
  | Eq   -> "="
  | InEq -> "<>"

let pp_atom_pow fmt (a,e) =
  if BI.is_one e then
    pp_atom fmt a
  else
    F.fprintf fmt "%a^%s" pp_atom a (BI.to_string e)

let pp_monom fmt (mon : monom) =
  if (Map.to_alist mon.monom_map)<>[] then
    F.fprintf fmt "@[<hov 2>%a@]"
      (pp_list " * " pp_atom_pow) (Map.to_alist mon.monom_map)
  else
    F.fprintf fmt "@[<hov 2>1@]"

let pp_binder s fmt vars =
  if vars = []
  then pp_string fmt ""
  else F.fprintf fmt "%s %a: " s (pp_list "," pp_ivar) vars

let pp_sum fmt sum =
  if sum.ivars<>[] && sum.i_ineq<>[] then
    F.fprintf fmt "@[<hov 2>(%a(%a) %a)@]"
      (pp_binder "sum") sum.ivars
      (pp_list ", " pp_ivar_pair) sum.i_ineq
      pp_monom sum.monom
  else if sum.ivars <> [] then
      F.fprintf fmt "@[<hov 2>(%a%a)@]"
      (pp_binder "sum") sum.ivars
      pp_monom sum.monom
  else if sum.i_ineq <> [] then
      F.fprintf fmt "@[<hov 2>(%a)%a@]"
      (pp_list ", " pp_ivar_pair) sum.i_ineq
      pp_monom sum.monom
  else
    F.fprintf fmt "@[<hov 2>%a@]"
      pp_monom sum.monom

let pp_term fmt (s,c) =
  let one = mk_sum [] [] (mk_monom []) in
  if BI.is_one c then pp_sum fmt s
  else if Sum.equal s one then F.fprintf fmt "@[<hov 2>%s@]" (BI.to_string c)
  else F.fprintf fmt "@[<hov 2>%s * %a@]" (BI.to_string c) pp_sum s

let pp_poly fmt (poly : poly) =
  let mneg =
    Map.filter_map poly.poly_map
      ~f:(fun bi -> if BI.sign bi < 0 then Some (BI.opp bi) else None)
  in
  let mpos =
    Map.filter poly.poly_map
      ~f:(fun ~key:_k ~data:bi -> BI.sign bi >= 0)
  in
  match Map.to_alist mpos, Map.to_alist mneg with
  | [], [] ->
    F.fprintf fmt "0"
  | [], negs ->
    F.fprintf fmt "@[<hov 2>-(%a)@]" (pp_list "@ + " pp_term) negs
  | pos,[] ->
    F.fprintf fmt "@[<hov 2>%a@]" (pp_list "@ + " pp_term) pos
  | pos,negs ->
    F.fprintf fmt "@[<hov 2>%a@ - %a@]"
      (pp_list "@ + " pp_term) pos
      (pp_list "@ - " pp_term) negs

let pp_constr fmt { qvars = qvs; q_ineq = qinqs; poly = p; is_eq = is_eq } =
  if qinqs<>[] then
    F.fprintf fmt "@[<hov 2>%a(%a) %a %s 0@]"
      (pp_binder "forall") qvs
      (pp_list ", " pp_ivar_pair) qinqs
      pp_poly p
      (is_eq_to_string is_eq)
  else
    F.fprintf fmt "@[<hov 2>%a%a %s 0@]"
      (pp_binder "forall") qvs
      pp_poly p
      (is_eq_to_string is_eq)

let pp_constr_conj fmt conj =
  let rec aux n list f =
    match list with
    | [] -> F.fprintf f "\n"
    | c :: rest ->
      F.fprintf f "@[%i: %a@]@\n\n" n pp_constr c;
      F.fprintf f "%t" (aux (n+1) rest)
  in
  aux 1 conj fmt
