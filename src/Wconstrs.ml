open Core.Std
open Util
open Abbrevs
open Watom

(* ======================================================================= *)
(* constraint expressions and constraints  *)

type is_eq = Eq | InEq with compare, sexp

(* Mapping from atom to exponent, we ensure in mk_monom that only random
   variables can have negative exponents *)
type monom = BI.t Atom.Map.t with sexp, compare

(* [Sum ivars: monom] where monom can contain bound and free index variables *)
type sum = {
  ivars  : ivar list;
  monom  : monom;
} with compare, sexp

(* data structures with sums *)
module Sum = struct
  module T = struct
    type t = sum
    let compare = compare_sum
    let sexp_of_t = sexp_of_sum
    let t_of_sexp = sum_of_sexp
  end
  include T
  include Comparable.Make(T)
end

(* Mapping from term to coefficient, we ensure in mk_poly
   that coefficients cannot be zero *)
type poly = BI.t Sum.Map.t with compare, sexp

(* all-constraint in paper *)
type constr = {
  qvars  : ivar list;
  is_eq  : is_eq;
  poly   : poly;
} with compare, sexp

(* ----------------------------------------------------------------------- *)
(* variables occurences *)

let ivars_monom mon =
  Map.fold mon
    ~init:Ivar.Set.empty
    ~f:(fun ~key:k ~data:_v se -> Set.union se (ivars_atom k))

let ivars_sum sum =
  ivars_monom sum.monom

let ivars_poly poly =
  L.fold_left (Map.keys poly)
    ~init:Ivar.Set.empty
    ~f:(fun se1 t -> Set.union se1 (ivars_sum t))

let ivars_constr constr =
  ivars_poly constr.poly

(* ----------------------------------------------------------------------- *)
(* smart constructors *)

let mult_monom_atom m (e,a) =
    if BI.cmp e BI.zero < 0 && not (is_rvar a) then
      failwith "mk_monom: only random variables can have negative exponent";
    Map.change m a
      (function 
         | None   -> Some e
         | Some i -> 
           let i = BI.(i +! e) in
           if BI.is_zero i then None else Some i)

let mk_monom atoms =
  L.fold_left atoms
    ~init:Atom.Map.empty
    ~f:(fun m (inv,a) -> mult_monom_atom m (bi_of_inv inv,a))

let mk_sum ivs mon =
  let iv_occs = ivars_monom mon in
  let ivs = L.filter ~f:(fun iv -> Set.mem iv_occs iv) ivs in
  { ivars = ivs; monom = mon }

let poly_add m (c,t) =
  Map.change m t
    (function 
    | None    -> Some c
    | Some c' -> 
      let c = BI.(c +! c') in
      if BI.is_zero c then None else Some c)

let mk_poly terms =
  L.fold_left ~init:Sum.Map.empty ~f:poly_add terms

let mk_constr ivs is_eq poly =
  let iv_occs = ivars_poly poly in
  let ivs = L.filter ~f:(fun iv -> Set.mem iv_occs iv) ivs in
  { qvars = ivs; is_eq = is_eq; poly = poly }

(* ----------------------------------------------------------------------- *)
(* arithmetic operations *)

let opp_poly p =
  Map.map ~f:(fun coeff -> BI.opp coeff) p

let add_poly p1 p2 =
  let add_term ~key:_k = function
    | `Both(c1,c2) ->
      BI.(
        let c = c1 +! c2 in
        if is_zero c then None else Some c)
    | `Left c | `Right c -> Some c
  in
  Map.merge p1 p2 ~f:add_term

let minus_poly p1 p2 =
  add_poly p1 (opp_poly p2)

let mult_monom m1 m2 =
  let add_exp ~key:_k = function
    | `Both(e1,e2) ->
      BI.(
        let e = e1 +! e2 in
        if is_zero e then None else Some e)
    | `Left e | `Right e -> Some e
  in
  Map.merge m1 m2 ~f:add_exp

let map_idx_monom ~f m =
  Atom.Map.fold m
    ~init:Atom.Map.empty
    ~f:(fun ~key:a ~data:bi m -> mult_monom_atom m (bi,Watom.map_idx ~f a))

let new_ivar taken old_idx =
  let n = old_idx.name in
  let rec go i =
    let idx = { name = n; id = i } in
    if Set.mem taken idx then
      go (i+1)
    else
      idx
  in
  go 0

let renaming_away_from taken ivars =
  Set.fold ivars ~init:(Ivar.Map.empty,taken)
    ~f:(fun (m,taken) ivar ->
      let ivar' = new_ivar taken ivar in
      (Map.add m ~key:ivar ~data:ivar', Set.add taken ivar'))

let rename rn ivar =
  Option.value ~default:ivar (Map.find rn ivar)

let mult_sum s1 s2 =
  (* rename bound variables in s1 and s2 *)
  let free_vars =
    Set.union
      (Set.diff (ivars_sum s1) (Ivar.Set.of_list s1.ivars))
      (Set.diff (ivars_sum s2) (Ivar.Set.of_list s2.ivars))
  in
  let (rn1,taken) = renaming_away_from free_vars (Ivar.Set.of_list s1.ivars) in
  let ivars1 = L.map s1.ivars ~f:(rename rn1) in
  let monom1 = map_idx_monom  ~f:(rename rn1) s1.monom in
  let (rn2,_) = renaming_away_from taken (Ivar.Set.of_list s2.ivars) in
  let ivars2 = L.map s2.ivars ~f:(rename rn2)in
  let monom2 = map_idx_monom ~f:(rename rn2) s2.monom in
  mk_sum (ivars1 @ ivars2) (mult_monom monom1 monom2)

let mult_term (c1,s1) (c2,s2) =
  (BI.(c1 *! c2), mult_sum s1 s2)

let mult_poly_term p (c0,s0) =
  Map.fold p
    ~init:(mk_poly [])
    ~f:(fun ~key:s ~data:c p ->
          let p' = mk_poly [mult_term (c0,s0) (c,s)] in
          add_poly p p')

let mult_poly p1 p2 =
  Map.fold p1
    ~init:(mk_poly [])
    ~f:(fun ~key:s ~data:c p ->
          let p' = mult_poly_term p2 (c,s) in
          add_poly p p')

module SP = struct
  let ( *! ) a b = mult_poly a b
  let ( +! ) a b = add_poly a b
  let ( -! ) a b = minus_poly a b
  let zero = mk_poly []

  (* define shortcut poly constructors *)
  let of_term c m = mk_poly [(c, mk_sum [] (mk_monom m))]
  let of_const c  = of_term c []
  let of_monom m  = of_term BI.one m
  let of_a a = of_term BI.one [(NoInv,a)]
  let sum ivs p =
    Map.fold p
      ~init:zero
      ~f:(fun ~key:sum ~data:c new_p ->
            poly_add new_p (c,(mk_sum (ivs@sum.ivars) sum.monom)))

  let one = of_const BI.one
end

(* ----------------------------------------------------------------------- *)
(* useful functions *)

let subst_idx (_c : constr) (_i : ivar) (_j : ivar) =
  failwith "undefined"

let subst (_c : constr) (_p : param) =
  failwith "undefined"

let split (_iv : ivar) (_c : constr) =
  failwith "undefined"

(* ----------------------------------------------------------------------- *)
(* pretty printing *)

let is_eq_to_string = function
  | Eq   -> "="
  | InEq -> "<>"

let pp_atom_pow fmt (a,e) =
  if BI.is_one e then
    pp_atom fmt a
  else
    F.fprintf fmt "%a^%s" pp_atom a (BI.to_string e)

let pp_monom fmt mon =
  F.fprintf fmt "@[<hv 2>%a@]"
    (pp_list " * " pp_atom_pow) (Map.to_alist mon)

let pp_binder s fmt vars =
  if vars = []
  then pp_string fmt ""
  else F.fprintf fmt "%s %a: " s (pp_list "," pp_ivar) vars

let pp_sum fmt sum =
  if sum.ivars<>[] then 
    F.fprintf fmt "@[<hov 2>(%a%a)@]"
      (pp_binder "sum") sum.ivars
      pp_monom sum.monom
  else
    F.fprintf fmt "@[<hov 2>%a@]"
      pp_monom sum.monom

let pp_term fmt (s,c) =
  if BI.is_one c
  then pp_sum fmt s
  else F.fprintf fmt "@[<hov 2>%s * %a@]" (BI.to_string c) pp_sum s

let pp_poly fmt poly =
  let mneg = Map.filter_map poly
    ~f:(fun bi -> if BI.(cmp bi zero < 0) then Some (BI.opp bi) else None)
  in
  let mpos = Map.filter poly ~f:(fun ~key:_k ~data:bi -> BI.(cmp bi zero >= 0)) in
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

let pp_constr fmt { qvars = qvs; poly = p; is_eq = is_eq } =
  F.fprintf fmt "@[<hv 2>%a%a %s 0@]" (pp_binder "forall") qvs pp_poly p (is_eq_to_string is_eq)
