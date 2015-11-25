(* * Constraints and operations on constraints *)

open Core_kernel.Std
open Util
open Watom

(* ** Constraint expressions and constraints
 * ======================================================================= *)

type is_eq = Eq | InEq
  with sexp, compare
val equal_is_eq : is_eq -> is_eq -> bool

type monom = private { monom_map : BI.t Atom.Map.t }
  with sexp, compare
val equal_monom : monom -> monom -> bool

type umonom = private { umonom_map : BI.t Uvar.Map.t }
  with sexp, compare
val equal_umonom : umonom -> umonom -> bool

type coeff = private { coeff_unif : umonom ; coeff_mon : monom }
  with sexp, compare
val equal_coeff : coeff -> coeff -> bool

type summand = Mon of monom | Coeff of coeff
  with sexp, compare
val equal_summand : summand -> summand -> bool

type sum = private { sum_ivarsK : (ivar * Ivar.Set.t) list; sum_summand : summand; }
  with sexp, compare
val equal_sum : sum -> sum -> bool

module Sum : sig
  include Comparable.S with type t := sum
end

type poly = private { poly_map : BI.t Sum.Map.t }
  with sexp, compare
val equal_poly : poly -> poly -> bool

type constr = private { constr_ivarsK : (ivar * Ivar.Set.t) list; constr_is_eq : is_eq; constr_poly : poly; }
  with sexp, compare
val equal_constr : constr -> constr -> bool

type conj = private { conj_ivarsK : (ivar * Ivar.Set.t) list; conj_constrs : constr list; }
  with sexp, compare

val equal_conj : conj -> conj -> bool

(* ** Extracting, mapping, and renaming index variables
 * ----------------------------------------------------------------------- *)

val mon2umon : monom  -> umonom
val umon2mon : umonom -> monom

val monom_filter_vars : (atom -> bool) -> monom -> monom

val ivars_monom  : monom       -> Ivar.Set.t
val ivars_umonom : umonom      -> Ivar.Set.t
val ivars_sum    : sum         -> Ivar.Set.t
val ivars_poly   : poly        -> Ivar.Set.t
val ivars_constr : constr      -> Ivar.Set.t
val ivars_conj   : conj        -> Ivar.Set.t

val renaming_away_from : Ivar.Set.t -> Ivar.Set.t ->  ivar Ivar.Map.t * Ivar.Set.t
val apply_renaming : ivar Ivar.Map.t -> ivar -> ivar

val map_idx_monom   : f:(ivar -> ivar) -> monom   -> monom
val map_idx_umonom  : f:(ivar -> ivar) -> umonom  -> umonom
val map_idx_coeff   : f:(ivar -> ivar) -> coeff   -> coeff
val map_idx_summand : f:(ivar -> ivar) -> summand -> summand
val map_idx_sum     : f:(ivar -> ivar) -> sum     -> sum
val map_idx_poly    : f:(ivar -> ivar) -> poly    -> poly

val map_atom_monom : f:(key:atom -> data:BI.t -> Big_int.big_int Watom.Atom.Map.t -> Big_int.big_int Watom.Atom.Map.t)
  -> monom -> monom

val new_ivar : Ivar.Set.t -> ivar -> ivar

(* ** Smart constructors
 * ----------------------------------------------------------------------- *)

val mk_monom  : (inv * atom) list -> monom
val mk_coeff  : umonom -> monom -> coeff
val mk_sum    : (ivar * Ivar.Set.t) list -> summand -> sum
val mk_poly   : (BI.t * sum) list -> poly
val mk_constr : (ivar * Ivar.Set.t) list -> is_eq -> poly -> constr
val mk_conj   : (ivar * Ivar.Set.t) list -> constr list -> conj

val mk_monom_of_map : BI.t Atom.Map.t -> monom
val mk_poly_of_map  : BI.t Sum.Map.t  -> poly 

(* val all_pairs: ivar list -> ivar_pair list *)
(* val all_ivar_distinct_poly : poly -> poly *)

(* ** Arithmetic operations
 * ----------------------------------------------------------------------- *)

val inv_monom : monom -> monom
val inv_umonom : umonom -> umonom
val mult_monom_atom : monom -> BI.t * atom -> monom
val add_poly_term : poly ->  BI.t * sum -> poly
val mult_monom : monom -> monom -> monom
val mult_umonom : umonom -> umonom -> umonom
val mult_summand : summand -> summand -> summand
val mult_sum : sum -> sum -> sum
val mult_term : BI.t * sum -> BI.t * sum -> BI.t * sum

(* val all_ivar_distinct_constr_conj : constr list -> constr list *)

module SP : sig
  val ( *! ) : poly -> poly -> poly
  val ( +! ) : poly -> poly -> poly
  val ( -! ) : poly -> poly -> poly
  val zero : poly
  val one : poly
  val opp : poly -> poly
  val of_coeff_monom : BI.t -> (inv * atom) list -> poly
  val of_const : BI.t -> poly
  val of_monom : (inv * atom) list -> poly
  val of_atom : atom -> poly
end
