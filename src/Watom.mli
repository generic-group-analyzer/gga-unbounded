(* * Atoms: Variables and parameters *)

(* ** Imports *)
open Core_kernel.Std
open Util
open Abbrevs

(* ** Variables and parameters
 * ----------------------------------------------------------------------- *)

type inv = NoInv | Inv with compare, sexp

type group_name = G1 | G2 with compare, sexp

type group_setting = I | II | III with compare, sexp

type ty = Fp | GroupName of group_name with compare, sexp

type ivar = { name : string; id : int } with compare, sexp

module Ivar : sig
  include Comparable.S with type t := ivar
end

(*
type ivar_pair = ivar * ivar with compare, sexp

module Ivar_Pair : sig
  include Comparable.S with type t := ivar_pair
end
*)
type name_oidx = string * ivar option with compare, sexp

type uvar = name_oidx with compare, sexp

type param = name_oidx with compare, sexp

type hvar = { hv_name : string; hv_ivar : ivar; hv_gname : group_name }
  with compare, sexp

type atom =
  | Param of param
  | Uvar of uvar
  | Hvar of hvar
  with compare, sexp

module Atom : sig
  include Comparable.S with type t := atom
end

module Uvar : sig
  include Comparable.S with type t := uvar
end

val equal_inv           : inv           -> inv           -> bool
val equal_group_name    : group_name    -> group_name    -> bool
val equal_group_setting : group_setting -> group_setting -> bool
val equal_ty            : ty            -> ty            -> bool
val equal_ivar          : ivar          -> ivar          -> bool
(*val equal_ivar_pair     : ivar * ivar   -> ivar * ivar   -> bool *)
val equal_uvar          : uvar          -> uvar          -> bool
val equal_param         : param         -> param         -> bool
val equal_hvar          : hvar          -> hvar          -> bool
val equal_atom          : atom          -> atom          -> bool

(* ** Destructors, indicators, map functions
 * ----------------------------------------------------------------------- *)

val is_uvar   : atom -> bool
val is_param  : atom -> bool
val is_hvar   : atom -> bool

val bi_of_inv : inv -> BI.t

val ivars_atom : atom -> Ivar.Set.t

val map_idx  : f:(ivar -> ivar) -> atom -> atom

(* ** Constructors
 * ----------------------------------------------------------------------- *)

val mk_uvar  : ?idx:ivar option -> string               -> atom
val mk_param : ?idx:ivar option -> string               -> atom
val mk_hvar  : idx:ivar         -> group_name -> string -> atom


(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

val pp_gname     : F.formatter -> group_name -> unit
val pp_ivar      : F.formatter -> ivar -> unit
val pp_name_idx  : F.formatter -> string * ivar -> unit
val pp_name_oidx : F.formatter -> string * ivar option -> unit
(* val pp_ivar_pair : F.formatter -> ivar_pair-> unit *)
val pp_uvar      : F.formatter -> string * ivar option -> unit
val pp_param     : F.formatter -> string * ivar option -> unit
val pp_hvar      : F.formatter -> hvar -> unit
val pp_inv       : F.formatter -> inv -> unit
val pp_atom      : F.formatter -> atom -> unit
