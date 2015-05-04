open Core.Std
open Big_int
open Util
open Abbrevs

(* ======================================================================= *)
(* Variables and parameters *)

type inv = NoInv | Inv with compare, sexp

type group_name = G1 | G2 with compare, sexp

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

(* random variable (possibly indexed) *)
type rvar = name_oidx with compare, sexp

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
  | Rvar  of rvar
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

(* ----------------------------------------------------------------------- *)
(* Destructors, indicators *)

let bi_of_inv = function
  | Inv   -> BI.of_int (-1)
  | NoInv -> BI.one

let is_rvar = function Rvar _ -> true | _ -> false

let is_param = function Param _ -> true | _ -> false

let is_hvar = function Hvar _ -> true | _ -> false

let ivars_atom = function
  | Rvar (_,Some i)
  | Param (_,Some i) -> Ivar.Set.singleton i
  | Hvar hv          -> Ivar.Set.singleton hv.hv_ivar
  | _                -> Ivar.Set.empty

(* ----------------------------------------------------------------------- *)
(* Constructors *)

let mk_rvar ?idx:(idx=None) name =
  Rvar (name,idx)

let mk_param ?idx:(idx=None) name = Param (name,idx)

let mk_hvar ~idx gname name =
  Hvar {hv_name = name; hv_ivar = idx; hv_gname = gname }

let map_idx ~f = function
  | Rvar (v,Some i)  -> Rvar (v,Some (f i))
  | Param (v,Some i) -> Param (v,Some (f i))
  | Hvar hv          -> Hvar { hv with hv_ivar = f hv.hv_ivar }
  | a                -> a
  
(* ----------------------------------------------------------------------- *)
(* Pretty printing *)

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

let pp_rvar = pp_name_oidx

let pp_param = pp_name_oidx

let pp_hvar fmt { hv_name=s; hv_ivar=i; hv_gname=gn } =
  F.fprintf fmt "%s_%a@%a" s pp_ivar i pp_gname gn

let pp_inv fmt = function
  | NoInv -> pp_string fmt "NoInv"
  | Inv   -> pp_string fmt "Inv"

let pp_atom fmt = function
  | Rvar(vi)  -> F.fprintf fmt "%a" pp_rvar vi
  | Param(vi) -> F.fprintf fmt "%a" pp_param vi
  | Hvar(hv)  -> F.fprintf fmt "%a" pp_hvar hv
