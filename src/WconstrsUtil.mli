(* * Constraints and operations on constraints *)

open Util
open Wconstrs
open Watom


(* ** Matching and Isomorphisms
 * ----------------------------------------------------------------------- *)

val matching_poly   : poly   -> poly   -> ivar Ivar.Map.t list
val matching_constr : constr -> constr -> ivar Ivar.Map.t list

val isomorphic_sum    : sum    -> sum    -> bool
val isomorphic_poly   : poly   -> poly   -> bool
val isomorphic_constr : constr -> constr -> bool


(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

val is_eq_to_string : is_eq -> string
val pp_binder       : string -> Format.formatter -> ivar list -> unit
val pp_atom_pow     : Format.formatter -> atom * BI.t -> unit
val pp_monom        : Format.formatter -> monom       -> unit
val pp_sum          : Format.formatter -> sum         -> unit
val pp_term         : Format.formatter -> sum * BI.t  -> unit
val pp_poly         : Format.formatter -> poly        -> unit
val pp_constr       : Format.formatter -> constr      -> unit
val pp_constr_conj  : Format.formatter -> constr list -> unit
