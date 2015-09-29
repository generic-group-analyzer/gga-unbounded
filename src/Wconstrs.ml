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

let monom_of_map m = { monom_map = m } (* DO NOT EXPORT *)

(* [Sum ivars: monom] where monom can contain bound and free index variables *)
type sum = {
  ivars  : ivar list;
  i_ineq : ivar_pair list;
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
type poly = { poly_map : BI.t Sum.Map.t }
  with compare, sexp

let poly_of_map m = { poly_map = m } (* DO NOT EXPORT *)

(* forall-constraint in paper *)
type constr = {
  qvars  : ivar list;
  q_ineq : ivar_pair list;
  is_eq  : is_eq;
  poly   : poly;
} with compare, sexp

(* constraint conjunction *)
type constr_conj = constr list with compare, sexp

(* ** Equality functions
 * ----------------------------------------------------------------------- *)

let equal_is_eq       a b = compare_is_eq       a b = 0
let equal_monom       a b = compare_monom       a b = 0
let equal_sum         a b = compare_sum         a b = 0
let equal_poly        a b = compare_poly        a b = 0
let equal_constr      a b = compare_constr      a b = 0
let equal_constr_conj a b = compare_constr_conj a b = 0

(* ** Extracting index variables (all, free, bound)
 * ----------------------------------------------------------------------- *)

let ivars_pairs pairs =
  L.fold_left pairs
   ~init:Ivar.Set.empty
   ~f:(fun s (i,j) -> Set.union s (Ivar.Set.of_list [i;j]))

let ivars_monom (mon : monom) =
  Map.fold mon.monom_map
    ~init:Ivar.Set.empty
    ~f:(fun ~key:k ~data:_v se -> Set.union se (ivars_atom k))

let ivars_sum sum =
  Set.union (ivars_monom sum.monom) (Ivar.Set.of_list sum.ivars)
  (*FIXME: add |> Set.union (ivars_pairs sum.i_ineq)? *)

let ivars_poly (poly : poly) =
  Map.fold poly.poly_map
    ~init:Ivar.Set.empty
    ~f:(fun ~key:sum ~data:_v se1 ->
           Set.union se1 (ivars_sum sum)
           |> Set.union (ivars_pairs sum.i_ineq))
           (* FIXME: why ineq included here, but not before *)

let ivars_constr constr =
  Set.union (ivars_poly constr.poly) (Ivar.Set.of_list constr.qvars)
  (* FIXME: why ineq not included here, but before *)

let ivars_conj conj =
  L.fold_left conj
    ~init:Ivar.Set.empty
    ~f:(fun se1 t -> Set.union se1 (ivars_constr t))

let free_ivars_sum s =
  Set.diff (ivars_sum s) (Ivar.Set.of_list s.ivars)

let free_ivars_poly (poly : poly) =
  Map.fold poly.poly_map
    ~init:Ivar.Set.empty
    ~f:(fun ~key:s ~data:_c se -> Set.union se (free_ivars_sum s))

let free_ivars_constr c =
  Set.diff (free_ivars_poly c.poly) (Ivar.Set.of_list c.qvars)

let free_ivars_constr_conj constraints =
  L.fold_left constraints
    ~init:Ivar.Set.empty
    ~f:(fun s c -> Set.union s (free_ivars_constr c))

let bound_ivars_poly (poly : poly) =
  Map.fold poly.poly_map
    ~init:Ivar.Set.empty
    ~f:(fun ~key:s ~data:_c se -> Set.union se (Ivar.Set.of_list s.ivars))

let bound_ivars_constr_conj constraints =
  L.fold_left constraints
    ~init:Ivar.Set.empty
    ~f:(fun se c ->
          Set.union se (bound_ivars_poly c.poly)
          |> Set.union (Ivar.Set.of_list c.qvars))

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

let mk_sum ivars i_ineq (mon : monom) =
  let ivars_set = Set.inter (Ivar.Set.of_list ivars) (ivars_monom mon) in
  let i_ineq =
    L.filter i_ineq ~f:(fun (i,j) -> Set.mem ivars_set i || Set.mem ivars_set j)
  in
  { ivars = Set.to_list ivars_set; i_ineq = i_ineq; monom = mon }

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

let mk_constr qvars q_ineq is_eq (poly : poly) =
  let qvars_set = Set.inter (Ivar.Set.of_list qvars) (ivars_poly poly) in
  let q_ineq =
    L.filter q_ineq ~f:(fun (i,j) -> Set.mem qvars_set i || Set.mem qvars_set j)
    |> L.dedup ~compare:Ivar_Pair.compare
  in
  { qvars = Set.to_list qvars_set; q_ineq = q_ineq; is_eq = is_eq; poly = poly }

(* ** Arithmetic operations
 * ----------------------------------------------------------------------- *)

let map_idx_monom ~f (m : monom) =
  Map.fold m.monom_map
    ~init:(monom_of_map Atom.Map.empty)
    ~f:(fun ~key:a ~data:bi m -> mult_monom_atom m (bi,Watom.map_idx ~f a))

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
  mk_sum
    (L.map ~f s.ivars)
    (L.map ~f:(fun(x,y) -> (f x, f y)) s.i_ineq)
    (map_idx_monom ~f s.monom)

let map_idx_poly ~f (p : poly) =
  Map.fold p.poly_map
    ~init:zero_poly
    ~f:(fun ~key:s ~data:c p' -> add_poly_term p' (c, map_idx_sum ~f s))

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

let mult_sum s1 s2 =
  let free_vars = Set.union (free_ivars_sum s1) (free_ivars_sum s2) in
  let (rn1,taken) = renaming_away_from free_vars (Ivar.Set.of_list s1.ivars) in
  let ivars1 = L.map s1.ivars ~f:(apply_renaming rn1) in
  let i_ineq1 = L.map s1.i_ineq ~f:(fun (x,y) -> (apply_renaming rn1 x, apply_renaming rn1 y)) in
  let monom1 = map_idx_monom  ~f:(apply_renaming rn1) s1.monom in
  let (rn2,_) = renaming_away_from taken (Ivar.Set.of_list s2.ivars) in
  let ivars2 = L.map s2.ivars ~f:(apply_renaming rn2)in
  let i_ineq2 = L.map s2.i_ineq ~f:(fun (x,y) -> (apply_renaming rn2 x, apply_renaming rn2 y)) in
  let monom2 = map_idx_monom ~f:(apply_renaming rn2) s2.monom in
  mk_sum (ivars1 @ ivars2) (i_ineq1 @ i_ineq2) (mult_monom monom1 monom2)

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
  let of_coeff_monom c m = mk_poly [(c, mk_sum [] [] (mk_monom m))]
  let of_const c  = of_coeff_monom c []
  let of_monom m  = of_coeff_monom BI.one m
  let of_atom a = of_monom [(NoInv,a)]
  let sum ivs p =
    Map.fold p.poly_map
      ~init:zero
      ~f:(fun ~key:sum ~data:c new_p ->
            add_poly_term new_p (c,(mk_sum (ivs@sum.ivars) [] sum.monom)))
  let one = of_const BI.one
end

(* ** Renaming: II
 * ----------------------------------------------------------------------- *)

let rename_sum s rn =
  let ivars = L.map s.ivars ~f:(apply_renaming rn) in
  let i_ineq = L.map s.i_ineq ~f:(fun (x,y) -> (apply_renaming rn x, apply_renaming rn y)) in
  let monom = map_idx_monom ~f:(apply_renaming rn) s.monom in
  mk_sum ivars i_ineq monom

let rename_poly (p : poly) rn =
  Map.fold p.poly_map
     ~init:SP.zero
     ~f:(fun ~key:s ~data:c p' -> SP.(p' +! (mk_poly [(c,rename_sum s rn)]) ) )

let rename_constr c rn =
  let qvars = L.map c.qvars ~f:(apply_renaming rn) in
  let q_ineq = L.map c.q_ineq ~f:(fun (x,y) -> (apply_renaming rn x, apply_renaming rn y)) in
  let poly = rename_poly c.poly rn in
  mk_constr qvars q_ineq c.is_eq poly
