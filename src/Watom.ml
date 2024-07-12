(* * Atoms: Variables and parameters *)

(* ** Imports *)
open Core
open Util

(* ** Variables and parameters
 * ----------------------------------------------------------------------- *)

type inv = NoInv | Inv [@@deriving compare, sexp]

(* group settings *)

type group_name = G1 | G2[@@deriving compare, sexp, hash]
type group_setting = I | II | III[@@deriving compare, sexp]
type ty = Fp | GroupName of group_name[@@deriving compare, sexp]

(* index variables *)
type ivar = {
  name : string;
  id : int;
}[@@deriving compare, sexp, hash]

(* data structures for ivar *)
module Ivar = struct
  module T = struct
    type t = ivar
    let compare = compare_ivar
    let sexp_of_t = sexp_of_ivar
    let t_of_sexp = ivar_of_sexp
  end
  include T
  include Comparable.Make(T)
end

(* name with optional index *)
type name_oidx = string * ivar option[@@deriving compare, sexp, hash]

(* uniform variable (possibly indexed) *)
type uvar = name_oidx[@@deriving compare, sexp, hash]

(* parameter (possibly indexed) *)
type param = name_oidx[@@deriving compare, sexp, hash]

(* handle variables *)
type hvar = {
  hv_name : string;
  hv_ivar : ivar;
  hv_gname : group_name
}[@@deriving compare, sexp, hash]

type atom =
  | Param of param
  | Uvar  of uvar
  | Hvar  of hvar
 [@@deriving compare, sexp, hash]

(* data structures with atoms *)
module Atom = struct
  module T = struct
    type t = atom
    let compare = compare_atom
    let sexp_of_t = sexp_of_atom
    let t_of_sexp = atom_of_sexp
    let hash_fold_t = hash_fold_atom
  end
  include T
  include Comparable.Make(T)
end

module ProvideHashAtomMap = Atom.Map.Provide_hash(Atom.T)
let hash_fold_atom_map = ProvideHashAtomMap.hash_fold_t

(* data structures with atoms *)
module Uvar = struct
  module T = struct
    type t = uvar
    let compare = compare_uvar
    let sexp_of_t = sexp_of_uvar
    let t_of_sexp = uvar_of_sexp
    let hash_fold_t = hash_fold_uvar
  end
  include T
  include Comparable.Make(T)
end

module ProvideHashUvarMap = Uvar.Map.Provide_hash(Uvar.T)
let hash_fold_uvar_map = ProvideHashUvarMap.hash_fold_t

let equal_inv           x y = compare_inv           x y = 0
let equal_group_name    x y = compare_group_name    x y = 0
let equal_group_setting x y = compare_group_setting x y = 0
let equal_ty            x y = compare_ty            x y = 0
let equal_ivar          x y = compare_ivar          x y = 0
let equal_uvar          x y = compare_uvar          x y = 0
let equal_param         x y = compare_param         x y = 0
let equal_hvar          x y = compare_hvar          x y = 0
let equal_atom          x y = compare_atom          x y = 0

(* ** Destructors, indicators
 * ----------------------------------------------------------------------- *)

let is_uvar  = function Uvar _  -> true | _ -> false
let is_param = function Param _ -> true | _ -> false
let is_hvar  = function Hvar _  -> true | _ -> false

let bi_of_inv = function
  | Inv   -> BI.of_int (-1)
  | NoInv -> BI.one

let ivars_atom = function
  | Uvar (_,Some i)
  | Param (_,Some i) -> Ivar.Set.singleton i
  | Hvar hv          -> Ivar.Set.singleton hv.hv_ivar
  | _                -> Ivar.Set.empty

let atom_name = function
  | Uvar (name, _) -> name
  | Param (name, _) -> name
  | Hvar hv -> hv.hv_name

(* ** Constructors
 * ----------------------------------------------------------------------- *)

let mk_uvar ?idx:(idx=None) name =
  Uvar (name,idx)

let mk_param ?idx:(idx=None) name = Param (name,idx)

let mk_hvar ~idx gname name =
  Hvar {hv_name = name; hv_ivar = idx; hv_gname = gname }

let map_idx ~f = function
  | Uvar (v,Some i)  -> Uvar (v,Some (f i))
  | Param (v,Some i) -> Param (v,Some (f i))
  | Hvar hv          -> Hvar { hv with hv_ivar = f hv.hv_ivar }
  | a                -> a
