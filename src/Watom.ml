(* * Atoms: Variables and parameters *)

(* ** Imports *)
open Core_kernel.Std
open Util
open Abbrevs

(* ** Variables and parameters
 * ----------------------------------------------------------------------- *)

type inv = NoInv | Inv with compare, sexp

(* group settings *)

type group_name = G1 | G2 with compare, sexp
type group_setting = I | II | III with compare, sexp
type ty = Fp | GroupName of group_name with compare, sexp

(* index variables *)
type ivar = {
  name : string;
  id : int;
} with compare, sexp

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
type name_oidx = string * ivar option with compare, sexp

(* uniform variable (possibly indexed) *)
type uvar = name_oidx with compare, sexp

(* parameter (possibly indexed) *)
type param = name_oidx with compare, sexp

(* handle variables *)
type hvar = {
  hv_name : string;
  hv_ivar : ivar;
  hv_gname : group_name
} with compare, sexp

type atom =
  | Param of param
  | Uvar  of uvar
  | Hvar  of hvar
  with compare, sexp

(* data structures with atoms *)
module Atom = struct
  module T = struct
    type t = atom
    let compare = compare_atom
    let sexp_of_t = sexp_of_atom
    let t_of_sexp = atom_of_sexp
  end
  include T
  include Comparable.Make(T)
end

(* data structures with atoms *)
module Uvar = struct
  module T = struct
    type t = uvar
    let compare = compare_uvar
    let sexp_of_t = sexp_of_uvar
    let t_of_sexp = uvar_of_sexp
  end
  include T
  include Comparable.Make(T)
end

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

(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

let pp_gname fmt = function
  | G1 -> pp_string fmt "G1"
  | G2 -> pp_string fmt "G2"

let pp_ivar fmt { name; id } =
  F.fprintf fmt "%s%s" name (String.make id '\'')

let pp_name_idx fmt (s,i) =
  F.fprintf fmt "%s_%a" s pp_ivar i

let pp_name_oidx fmt (s,oi) =
  match oi with
  | None   -> pp_string fmt s
  | Some i -> pp_name_idx fmt (s,i)

let pp_uvar = pp_name_oidx

let pp_param = pp_name_oidx

let pp_hvar fmt { hv_name=s; hv_ivar=i; hv_gname=gn } =
  F.fprintf fmt "%s_%a@%a" s pp_ivar i pp_gname gn

let pp_inv fmt = function
  | NoInv -> pp_string fmt "NoInv"
  | Inv   -> pp_string fmt "Inv"

let pp_atom fmt = function
  | Uvar(vi)  -> F.fprintf fmt "%a" pp_uvar vi
  | Param(vi) -> F.fprintf fmt "%a" pp_param vi
  | Hvar(hv)  -> F.fprintf fmt "%a" pp_hvar hv
