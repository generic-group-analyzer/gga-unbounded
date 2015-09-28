(* * Constraints and operations on constraints *)

open Core_kernel.Std
open Util
open Watom

(* ** Constraint expressions and constraints
 * ======================================================================= *)

type is_eq = Eq | InEq
  with sexp, compare
val equal_is_eq   : is_eq -> is_eq -> bool

type monom = BI.t Atom.Map.t
  with sexp, compare
val equal_monom   : monom -> monom -> bool

type sum = private { ivars : ivar list; i_ineq : ivar_pair list; monom : monom; }
  with sexp, compare
val equal_sum   : sum -> sum -> bool
val isomorphic_sum : sum -> sum -> bool

module Sum : sig
  include Comparable.S with type t := sum
end

type poly = BI.t Sum.Map.t
  with sexp, compare
val equal_poly   : poly -> poly -> bool
val matching_poly : poly -> poly -> ivar Ivar.Map.t list
val isomorphic_poly : poly -> poly -> bool

type constr = private { qvars : ivar list; q_ineq : ivar_pair list; is_eq : is_eq; poly : poly; }
  with sexp, compare
val equal_constr : constr -> constr -> bool
val matching_constr : constr -> constr -> ivar Ivar.Map.t list
val isomorphic_constr : constr -> constr -> bool

type constr_conj = constr list
  with sexp, compare
val equal_constr_conj : constr_conj -> constr_conj -> bool

(* ** Extracting, mapping, and renaming index variables
 * ----------------------------------------------------------------------- *)

val ivars_monom : monom -> Ivar.Set.t
val ivars_sum : sum -> Ivar.Set.t
val ivars_poly : poly  -> Ivar.Set.t
val ivars_constr : constr -> Ivar.Set.t
val ivars_conj : constr list -> Ivar.Set.t

val free_ivars_poly : poly -> Ivar.Set.t
val bound_ivars_poly : poly -> Ivar.Set.t
val free_ivars_constr : constr -> Ivar.Set.t
val free_ivars_constr_conj : constr_conj -> Ivar.Set.t
val bound_ivars_constr_conj : constr_conj -> Ivar.Set.t

val renaming_away_from : Ivar.Set.t -> Ivar.Set.t ->  ivar Ivar.Map.t * Ivar.Set.t
val apply_renaming : ivar Ivar.Map.t -> ivar -> ivar
val rename_sum : sum -> ivar Ivar.Map.t -> sum
val rename_poly : poly -> ivar Ivar.Map.t -> poly
val rename_constr : constr -> ivar Ivar.Map.t -> constr

val map_idx_monom : f:(ivar -> ivar) ->  monom -> monom
val map_idx_poly : f:(ivar -> ivar) ->  poly -> poly

val new_ivar : Ivar.Set.t -> ivar -> ivar

(* ** Smart constructors
 * ----------------------------------------------------------------------- *)

val mk_monom : (inv * atom) list -> BI.t Atom.Map.t
val mk_sum : ivar list -> ivar_pair list -> monom -> sum
val mk_poly : (BI.t * sum) list -> BI.t Sum.Map.t
val mk_constr : ivar list -> ivar_pair list -> is_eq -> poly -> constr

val all_pairs: ivar list -> ivar_pair list
val all_ivar_distinct_poly : poly -> poly

(* ** Arithmetic operations
 * ----------------------------------------------------------------------- *)

val mult_monom_atom : monom -> BI.t * atom -> monom
val add_poly_term : poly ->  BI.t * sum -> poly
val mult_monom : monom -> monom -> monom
val mult_sum : sum -> sum -> sum
val mult_term : BI.t * sum -> BI.t * sum -> BI.t * sum

val all_ivar_distinct_constr_conj : constr list -> constr list

module SP : sig
  val ( *! ) : poly -> poly -> poly
  val ( +! ) : poly -> poly -> poly
  val ( -! ) : poly -> poly -> poly
  val zero : BI.t Sum.Map.t
  val one : poly
  val opp : poly -> poly
  val of_coeff_monom : BI.t -> (inv * atom) list -> poly
  val of_const : BI.t -> poly
  val of_monom : (inv * atom) list -> poly
  val of_a : atom -> poly
  val sum : ivar list -> poly -> poly
end

(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

val is_eq_to_string : is_eq -> string
val pp_atom_pow : Format.formatter -> atom * BI.t -> unit
val pp_monom : Format.formatter -> (atom, BI.t, 'a) Core_kernel.Core_map.t -> unit
val pp_binder : string -> Format.formatter -> ivar list -> unit
val pp_sum : Format.formatter -> sum -> unit
val pp_term : Format.formatter -> sum * BI.t -> unit
val pp_poly : Format.formatter -> poly -> unit
val pp_constr : Format.formatter -> constr -> unit
val pp_constr_conj : Format.formatter -> constr list -> unit
