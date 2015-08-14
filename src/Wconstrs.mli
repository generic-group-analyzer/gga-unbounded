open Core.Std
open Util
open Watom

(* ======================================================================= *)
(* constraint expressions and constraints  *)

type is_eq = Eq | InEq

val is_eq_of_sexp : Sexplib.Type.t -> is_eq
val sexp_of_is_eq : is_eq -> Sexplib.Type.t
val compare_is_eq : is_eq -> is_eq -> int
val equal_is_eq   : is_eq -> is_eq -> bool

type monom = BI.t Atom.Map.t
val monom_of_sexp : Sexplib.Type.t -> monom
val sexp_of_monom : monom -> Sexplib.Type.t
val compare_monom : monom -> monom -> int
val equal_monom   : monom -> monom -> bool

type sum = private { ivars : ivar list; i_ineq : ivar_pair list; monom : monom; }
val sum_of_sexp : Sexplib.Type.t -> sum
val sexp_of_sum : sum -> Sexplib.Type.t
val compare_sum : sum -> sum -> int
val equal_sum   : sum -> sum -> bool
val isomorphic_sum : sum -> sum -> bool
				  
module Sum : sig
  include Comparable.S with type t := sum
end

type poly = BI.t Sum.Map.t
val poly_of_sexp : Sexplib.Type.t -> poly
val sexp_of_poly : poly -> Sexplib.Type.t
val compare_poly : poly -> poly -> int
val equal_poly   : poly -> poly -> bool
val matching_poly : poly -> poly -> ivar Ivar.Map.t list
val isomorphic_poly : poly -> poly -> bool

type constr = private { qvars : ivar list; q_ineq : ivar_pair list; is_eq : is_eq; poly : poly; }
val constr_of_sexp : Sexplib.Type.t -> constr
val sexp_of_constr : constr -> Sexplib.Type.t
val compare_constr : constr -> constr -> int
val equal_constr : constr -> constr -> bool
val matching_constr : constr -> constr -> ivar Ivar.Map.t list
val isomorphic_constr : constr -> constr -> bool
					       
type constr_conj = constr list
val constr_conj_of_sexp : Sexplib.Type.t -> constr_conj
val sexp_of_constr_conj : constr_conj -> Sexplib.Type.t
val compare_constr_conj : constr_conj -> constr_conj -> int
val equal_constr_conj   : constr_conj -> constr_conj -> bool

type constr_disj = constr_conj list
val constr_disj_of_sexp : Sexplib.Type.t -> constr_disj
val sexp_of_constr_disj : constr_disj -> Sexplib.Type.t
val compare_constr_disj : constr_disj -> constr_disj -> int
val equal_constr_disj   : constr_disj -> constr_disj -> bool

(* ----------------------------------------------------------------------- *)
(* extracting, mapping, and renaming index variables *)

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
					     
(* ----------------------------------------------------------------------- *)
(* smart constructors *)

val mk_monom : (inv * atom) list -> BI.t Atom.Map.t
val mk_sum : ivar list -> ivar_pair list -> monom -> sum
val mk_poly : (BI.t * sum) list -> BI.t Sum.Map.t
val mk_constr : ivar list -> ivar_pair list -> is_eq -> poly -> constr

val all_pairs: ivar list -> ivar_pair list
val all_ivar_distinct_poly : poly -> poly

(* ----------------------------------------------------------------------- *)
(* arithmetic operations *)

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

(* ----------------------------------------------------------------------- *)
(* pretty printing *)

val is_eq_to_string : is_eq -> string
val pp_atom_pow : Format.formatter -> atom * BI.t -> unit
val pp_monom : Format.formatter -> (atom, BI.t, 'a) Core_kernel.Core_map.t -> unit
val pp_binder : string -> Format.formatter -> ivar list -> unit
val pp_sum : Format.formatter -> sum -> unit
val pp_term : Format.formatter -> sum * BI.t -> unit
val pp_poly : Format.formatter -> poly -> unit
val pp_constr : Format.formatter -> constr -> unit
val pp_constr_conj : Format.formatter -> constr list -> unit
