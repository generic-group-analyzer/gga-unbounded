(* * Constraints and operations on constraints *)

(* ** Imports *)
open Core_kernel.Std
open Util
open Abbrevs
open Watom

(* ** Constraint expressions and constraints
 * ======================================================================= *)

type is_eq = Eq | InEq with compare, sexp

(* Mapping from atom to exponent, we ensure in mk_monom that only uniform
   variables can have negative exponents *)
type monom = { monom_map : BI.t Atom.Map.t }
  with compare, sexp

type umonom = { umonom_map : BI.t Uvar.Map.t }
 with compare, sexp

let monom_of_map  m = { monom_map  = m } (* DO NOT EXPORT *)

let monom_filter_vars p_var mon =
  monom_of_map (Map.filter mon.monom_map ~f:(fun ~key:k ~data:_d -> p_var k))

let umon2mon umonom =
  let new_keys = L.map (Map.keys umonom.umonom_map) ~f:(fun u -> Uvar(u)) in
  { monom_map = Atom.Map.of_alist_exn (L.zip_exn new_keys (Map.data umonom.umonom_map)) }

let mon2umon monom =
  let map_list = L.filter (Map.to_alist monom.monom_map) ~f:(fun (v,_) -> is_uvar v) in
  let uvar_f = function
    | Uvar(u) -> u
    | _ -> assert false
  in
  { umonom_map =  Uvar.Map.of_alist_exn (L.map map_list ~f:(fun (m,d) -> (uvar_f m,d))) }

type coeff = { coeff_unif : umonom ; coeff_mon : monom } with compare, sexp

type summand = Mon of monom | Coeff of coeff with compare, sexp

(* [Sum ivars: summand] where summand can contain bound and free index variables *)
type sum = {
  sum_ivarsK   : (ivar * Ivar.Set.t) list;
  sum_summand  : summand;
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
type poly = { poly_map : BI.t Sum.Map.t }
  with compare, sexp

let poly_of_map m = { poly_map = m } (* DO NOT EXPORT *)

(* forall-constraint in paper *)
type constr = {
  constr_ivarsK : (ivar * Ivar.Set.t) list;
  constr_is_eq  : is_eq;
  constr_poly   : poly;
} with compare, sexp

(* constraint conjunction *)
type conj = {
  conj_ivarsK  : (ivar * Ivar.Set.t) list;
  conj_constrs : constr list;
} with compare, sexp

(* ** Equality functions
 * ----------------------------------------------------------------------- *)

let equal_is_eq    a b = compare_is_eq    a b = 0
let equal_monom    a b = compare_monom    a b = 0
let equal_umonom   a b = compare_umonom   a b = 0
let equal_coeff    a b = compare_coeff    a b = 0
let equal_summand  a b = compare_summand  a b = 0
let equal_sum      a b = compare_sum      a b = 0
let equal_poly     a b = compare_poly     a b = 0
let equal_constr   a b = compare_constr   a b = 0
let equal_conj     a b = compare_conj     a b = 0

(* ** Extracting index variables (all, free, bound)
 * ----------------------------------------------------------------------- *)

let ivars_monom (mon : monom) =
  Map.fold mon.monom_map
    ~init:Ivar.Set.empty
    ~f:(fun ~key:k ~data:_v se -> Set.union se (ivars_atom k))

let ivars_umonom umon = ivars_monom (umon2mon umon)

let ivars_coeff (coeff : coeff) = ivars_monom coeff.coeff_mon

let ivars_summand = function
  | Mon(m) -> ivars_monom m
  | Coeff(c) -> ivars_coeff c

let ivars_sum sum =
  Set.union (ivars_summand sum.sum_summand) (Ivar.Set.of_list (unzip1 sum.sum_ivarsK))
  |> Set.union (L.fold_left (unzip2 sum.sum_ivarsK)
                 ~init:Ivar.Set.empty
                 ~f:Set.union
               )

let ivars_poly (poly : poly) =
  Map.fold poly.poly_map
    ~init:Ivar.Set.empty
    ~f:(fun ~key:sum ~data:_v se1 ->
           Set.union se1 (ivars_sum sum)
       )

let ivars_constr (constr : constr) =
  Set.union (ivars_poly constr.constr_poly) (Ivar.Set.of_list (unzip1 constr.constr_ivarsK))
  |> Set.union (L.fold_left (unzip2 constr.constr_ivarsK)
                 ~init:Ivar.Set.empty
                 ~f:Set.union
               )

let ivars_conj (conj : conj) =
  L.fold_left conj.conj_constrs
    ~init:Ivar.Set.empty
    ~f:(fun se1 t -> Set.union se1 (ivars_constr t))
  |> Set.union (Ivar.Set.of_list (unzip1 conj.conj_ivarsK))
  |> Set.union (L.fold_left (unzip2 conj.conj_ivarsK)
                 ~init:Ivar.Set.empty
                 ~f:Set.union
               )

(* ** Renaming: I
 * ----------------------------------------------------------------------- *)

let new_ivar taken old_idx =
  let n = old_idx.name in
  let rec go i =
    let idx = { name = n; id = i } in
    if Set.mem taken idx then
      go (i+1)
    else
      idx
  in
  go old_idx.id

let renaming_away_from taken ivars =
  Set.fold ivars ~init:(Ivar.Map.empty,taken)
    ~f:(fun (m,taken) ivar ->
          let ivar' = new_ivar taken ivar in
          (Map.add m ~key:ivar ~data:ivar', Set.add taken ivar'))

let apply_renaming rn ivar =
  Option.value ~default:ivar (Map.find rn ivar)

(* ** Smart constructors
 * ----------------------------------------------------------------------- *)

let mult_monom_atom m (e,a) =
    if BI.sign e < 0 && not (is_uvar a) then
      failwith "mult_monom_atom: only random variables can have negative exponent";
    Map.change m.monom_map a
      (function
       | None   -> Some e
       | Some i ->
         let i = BI.(i +! e) in
         if BI.is_zero i then None else Some i)
    |> monom_of_map

let mk_monom atoms =
  L.fold_left atoms
    ~init:(monom_of_map Atom.Map.empty)
    ~f:(fun m (inv,a) -> mult_monom_atom m (bi_of_inv inv,a))

let mk_coeff umonom monom =
  { coeff_unif = umonom ; coeff_mon = monom }

let well_formed_exceptions varsK =
  let rec aux indices sets =
    match indices, sets with
    | [], [] -> true
    | _i :: rest_indices, set :: rest_sets ->
      if (L.exists rest_indices ~f:(fun j -> Set.mem set j)) then false
      else aux rest_indices rest_sets
    | _ -> assert false
  in
  let indices, setsK = L.unzip varsK in
  aux indices setsK

let mk_sum ivarsK (summand : summand) =
  if (well_formed_exceptions ivarsK) then
    { sum_ivarsK = ivarsK; sum_summand = summand }
  else
    failwith "Not well formed sum"

let add_poly_term p (c,t) =
  poly_of_map
    (Map.change p.poly_map t
       (function
        | None    -> Some c
        | Some c' ->
          let c = BI.(c +! c') in
          if BI.is_zero c then None else Some c))

let zero_poly = poly_of_map Sum.Map.empty

let mk_poly terms =
  L.fold_left terms
    ~init:zero_poly
    ~f:add_poly_term

let mk_constr qvarsK is_eq (poly : poly) =
  let qvarsK = L.filter qvarsK ~f:(fun (i,_) -> Set.mem (ivars_poly poly) i) in
  if (well_formed_exceptions qvarsK) then
    { constr_ivarsK = qvarsK; constr_is_eq = is_eq; constr_poly = poly }
  else
    failwith "Not well formed constr"

let mk_conj fvarsK constrs =
  { conj_ivarsK = fvarsK; conj_constrs = constrs }

let mk_monom_of_map map =
  if L.exists (Map.data map) ~f:BI.is_zero then
    failwith "monom cannot containt a map to zero"
  else monom_of_map map

let mk_poly_of_map map =
  if L.exists (Map.data map) ~f:BI.is_zero then
    failwith "poly cannot containt a map to zero"
  else poly_of_map map

(* ** Arithmetic operations
 * ----------------------------------------------------------------------- *)

let inv_monom (m : monom) =
  monom_of_map (Map.map m.monom_map ~f:(fun e -> BI.opp e))

let inv_umonom (m : umonom) =
  mon2umon (inv_monom (umon2mon m))

let map_idx_monom ~f (m : monom) =
  Map.fold m.monom_map
    ~init:(monom_of_map Atom.Map.empty)
    ~f:(fun ~key:a ~data:bi m -> mult_monom_atom m (bi,Watom.map_idx ~f a))

let map_idx_umonom ~f (u : umonom) =
  mon2umon (map_idx_monom ~f (umon2mon u))

let map_idx_coeff ~f (c : coeff) =
  mk_coeff (map_idx_umonom ~f c.coeff_unif) (map_idx_monom ~f c.coeff_mon)

let map_idx_summand ~f = function
  | Mon(m) -> Mon(map_idx_monom ~f m)
  | Coeff(c) -> Coeff(map_idx_coeff ~f c)

let add_poly p1 p2 =
  let add_term ~key:_k = function
    | `Both(c1,c2) ->
      BI.(
        let c = c1 +! c2 in
        if is_zero c then None else Some c)
    | `Left c | `Right c -> if BI.is_zero c then None else Some c
  in
  poly_of_map (Map.merge p1.poly_map p2.poly_map ~f:add_term)

let map_idx_sum ~f (s : sum) =
  let ivars, isetsK = L.unzip s.sum_ivarsK in
  mk_sum
    (L.zip_exn (L.map ~f ivars) (L.map ~f:(Ivar.Set.map ~f) isetsK) )
    (map_idx_summand ~f s.sum_summand)

let map_idx_poly ~f (p : poly) =
  Map.fold p.poly_map
    ~init:zero_poly
    ~f:(fun ~key:s ~data:c p' -> add_poly_term p' (c, map_idx_sum ~f s))

let map_atom_monom ~f (m : monom) =
  monom_of_map (Map.fold m.monom_map ~init:Atom.Map.empty ~f)

let opp_poly p =
  poly_of_map (Map.map p.poly_map ~f:(fun coeff -> BI.opp coeff))

let minus_poly p1 p2 =
  add_poly p1 (opp_poly p2)

let mult_monom (m1 : monom) (m2 : monom) =
  let add_exp ~key:_k = function
    | `Both(e1,e2) ->
      BI.(
        let e = e1 +! e2 in
        if is_zero e then None else Some e)
    | `Left e | `Right e -> Some e
  in
  monom_of_map (Map.merge m1.monom_map m2.monom_map ~f:add_exp)

let mult_umonom (um1 : umonom) (um2 : umonom) =
  mon2umon (mult_monom (umon2mon um1) (umon2mon um2))

let mult_summand s1 s2 =
  match s1,s2 with
  | Mon(m1), Mon(m2) -> Mon(mult_monom m1 m2)
  | _ -> failwith "We don't allow multiplication of Coeff's"

let mult_sum s1 s2 =
  let used_vars = Set.union (ivars_sum s1) (ivars_sum s2) in
  let (rn1,taken) = renaming_away_from used_vars (Ivar.Set.of_list (unzip1 s1.sum_ivarsK)) in
  let ivars1 = L.map (unzip1 s1.sum_ivarsK) ~f:(apply_renaming rn1) in
  let isetsK1 = L.map (unzip2 s1.sum_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn1)) in
  let summand1 = map_idx_summand  ~f:(apply_renaming rn1) s1.sum_summand in
  let (rn2,_) = renaming_away_from taken (Ivar.Set.of_list (unzip1 s2.sum_ivarsK)) in
  let ivars2 = L.map (unzip1 s2.sum_ivarsK) ~f:(apply_renaming rn2)in
  let isetsK2 = L.map (unzip2 s2.sum_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn2)) in
  let summand2 = map_idx_summand ~f:(apply_renaming rn2) s2.sum_summand in
  mk_sum (L.zip_exn (ivars1 @ ivars2) (isetsK1 @ isetsK2)) (mult_summand summand1 summand2)

let mult_term (c1,s1) (c2,s2) =
  (BI.(c1 *! c2), mult_sum s1 s2)

let mult_poly_term (p : poly) (c0,s0) =
  Map.fold p.poly_map
    ~init:zero_poly
    ~f:(fun ~key:s ~data:c p -> add_poly_term p (mult_term (c0,s0) (c,s)))

let mult_poly p1 p2 =
  Map.fold p1.poly_map
    ~init:zero_poly
    ~f:(fun ~key:s ~data:c p -> add_poly p (mult_poly_term p2 (c,s)))

module SP = struct
  let ( *! ) a b = mult_poly a b
  let ( +! ) a b = add_poly a b
  let ( -! ) a b = minus_poly a b
  let opp a = opp_poly a
  let zero = zero_poly

  (* define shortcut poly constructors *)
  let of_coeff_monom c m = mk_poly [(c, mk_sum [] (Mon(mk_monom m)))]
  let of_const c  = of_coeff_monom c []
  let of_monom m  = of_coeff_monom BI.one m
  let of_atom a = of_monom [(NoInv,a)]
  let one = of_const BI.one
end
