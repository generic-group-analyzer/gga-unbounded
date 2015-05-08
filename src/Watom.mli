open Core.Std
open Util

(* ======================================================================= *)
(* Variables and parameters *)

type inv = NoInv | Inv
val inv_of_sexp : Sexplib.Type.t -> inv
val sexp_of_inv : inv -> Sexplib.Type.t
val compare_inv : inv -> inv -> int

type group_name = G1 | G2
val group_name_of_sexp : Sexplib.Type.t -> group_name
val sexp_of_group_name : group_name -> Sexplib.Type.t
val compare_group_name : group_name -> group_name -> int

type ivar = { name : bytes; id : int; }
val ivar_of_sexp : Sexplib.Type.t -> ivar
val sexp_of_ivar : ivar -> Sexplib.Type.t
val compare_ivar : ivar -> ivar -> int

module Ivar : sig
  include Comparable.S with type t := ivar
end

type ivar_pair = ivar * ivar
val ivar_pair_of_sexp : Sexplib.Type.t -> ivar * ivar
val sexp_of_ivar_pair : ivar * ivar -> Sexplib.Type.t
val compare_ivar_pair : ivar * ivar -> ivar * ivar -> int

module Ivar_Pair : sig
  include Comparable.S with type t := ivar_pair
end		

type name_oidx = bytes * ivar option
val name_oidx_of_sexp : Sexplib.Type.t -> name_oidx
val sexp_of_name_oidx : name_oidx -> Sexplib.Type.t
val compare_name_oidx : name_oidx -> name_oidx -> int

type rvar = name_oidx
val rvar_of_sexp : Sexplib.Type.t -> rvar
val sexp_of_rvar : rvar -> Sexplib.Type.t
val compare_rvar : rvar -> rvar -> int

type param = rvar
val param_of_sexp : Sexplib.Type.t -> param
val sexp_of_param : param -> Sexplib.Type.t
val compare_param : param -> param -> int

type hvar = {
  hv_name : bytes; hv_ivar : ivar; hv_gname : group_name;
}
val hvar_of_sexp : Sexplib.Type.t -> hvar
val sexp_of_hvar : hvar -> Sexplib.Type.t
val compare_hvar : hvar -> hvar -> int

type atom = Param of param | Rvar of param | Hvar of hvar
val atom_of_sexp : Sexplib.Type.t -> atom
val sexp_of_atom : atom -> Sexplib.Type.t
val compare_atom : atom -> atom -> int

module Atom : sig
  include Comparable.S with type t := atom
end

(* ----------------------------------------------------------------------- *)
(* Destructors, indicators *)

val bi_of_inv : inv -> BI.t
val is_rvar : atom -> bool
val is_param : atom -> bool
val is_hvar : atom -> bool

val ivars_atom : atom -> Ivar.Set.t

(* ----------------------------------------------------------------------- *)
(* Constructors *)

val mk_rvar : ?idx:ivar option -> bytes -> atom
val mk_param : ?idx:ivar option -> bytes -> atom
val mk_hvar : idx:ivar -> group_name -> bytes -> atom
val map_idx : f:(ivar -> ivar) -> atom -> atom

(* ----------------------------------------------------------------------- *)
(* Pretty printing *)

val pp_gname : Format.formatter -> group_name -> unit
val pp_ivar : Format.formatter -> ivar -> unit
val pp_name_idx : Format.formatter -> bytes * ivar -> unit
val pp_name_oidx : Format.formatter -> bytes * ivar option -> unit
val pp_ivar_pair : Format.formatter -> ivar_pair-> unit
val pp_rvar : Format.formatter -> bytes * ivar option -> unit
val pp_param : Format.formatter -> bytes * ivar option -> unit
val pp_hvar : Format.formatter -> hvar -> unit
val pp_inv : Format.formatter -> inv -> unit
val pp_atom : Format.formatter -> atom -> unit
