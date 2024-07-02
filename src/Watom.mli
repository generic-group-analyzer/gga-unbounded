(* * Atoms: Variables and parameters *)

(* ** Imports *)
open Core
open Util

(* ** Variables and parameters
 * ----------------------------------------------------------------------- *)

type inv = NoInv | Inv [@@deriving compare, sexp]

type group_name = G1 | G2[@@deriving compare, sexp]

type group_setting = I | II | III[@@deriving compare, sexp]

type ty = Fp | GroupName of group_name[@@deriving compare, sexp]

type ivar = { name : string; id : int }[@@deriving compare, sexp, hash]

module Ivar : sig
  include Comparable.S with type t := ivar
end

(*
type ivar_pair = ivar * ivar[@@deriving compare, sexp]

module Ivar_Pair : sig
  include Comparable.S with type t := ivar_pair
end
*)
type name_oidx = string * ivar option[@@deriving compare, sexp]

type uvar = name_oidx[@@deriving compare, sexp]

type param = name_oidx[@@deriving compare, sexp]

type hvar = { hv_name : string; hv_ivar : ivar; hv_gname : group_name }
 [@@deriving compare, sexp]

type atom =
  | Param of param
  | Uvar of uvar
  | Hvar of hvar
 [@@deriving compare, sexp]

module Atom : sig
  include Comparable.S with type t := atom
end
val hash_fold_atom_map: (Hash.state -> 'a -> Hash.state) -> Hash.state -> 'a Atom.Map.t -> Hash.state

module Uvar : sig
  include Comparable.S with type t := uvar
end
val hash_fold_uvar_map: (Hash.state -> 'a -> Hash.state) -> Hash.state -> 'a Uvar.Map.t -> Hash.state

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
val atom_name  : atom -> string

val map_idx  : f:(ivar -> ivar) -> atom -> atom

(* ** Constructors
 * ----------------------------------------------------------------------- *)

val mk_uvar  : ?idx:ivar option -> string               -> atom
val mk_param : ?idx:ivar option -> string               -> atom
val mk_hvar  : idx:ivar         -> group_name -> string -> atom
