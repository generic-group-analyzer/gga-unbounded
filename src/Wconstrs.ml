open Core.Std
open Big_int
open Util
open Abbrevs

(* ----------------------------------------------------------------------- *)

let big_int_of_sexp se = big_int_of_string (string_of_sexp se)

let sexp_of_big_int bi = sexp_of_string (string_of_big_int bi)

module BI = struct
  let one = unit_big_int
  let zero = zero_big_int
  let is_one = eq_big_int unit_big_int
  let ( *! ) a b = mult_big_int a b
  let of_int = big_int_of_int
  let cmp = compare_big_int
end

(* ----------------------------------------------------------------------- *)

type inv = NoInv | Inv with compare, sexp

type is_eq = Eq | InEq with compare, sexp

(* index variables *)
type ivar = string with compare, sexp

(* name with index *)
type name_idx = string * ivar with compare, sexp

(* name with optional index *)
type name_oidx = string * ivar option with compare, sexp

type rvar = name_oidx with compare, sexp

type param = name_oidx with compare, sexp

type hvar = name_idx with compare, sexp

type satom =
  | ARvar  of rvar * inv
  | AParam of param
  | AHvar  of hvar
  with compare, sexp

type smonom = { prod : satom list }
  with compare, sexp

type ssum =
  { ssum_bvar  : ivar list;
    ssum_expr  : smonom;
  }
  with compare, sexp

type sterm = (big_int * ssum)
  with compare, sexp

(* symbolic polynomial, contains \Sum *)
type spoly = { sum : sterm list }
  with compare, sexp

(* all-constraint in paper *)
type constr =
  { constr_bvars : ivar list;
    constr_is_eq : is_eq;
    constr_spoly  : spoly;
  }
  with compare, sexp

(* ----------------------------------------------------------------------- *)
(* constructor functions *)

let rvar ?inv:(inv=NoInv) name = ARvar ((name,None),inv)

let rvar_idx ?inv:(inv=NoInv) name idx = ARvar ((name,Some idx),inv)

let param name = AParam (name,None)

let param_idx name idx = AParam (name,Some idx)

let hvar name idx = AHvar (name,idx)

let ssum bvs e =
  { ssum_bvar  = bvs; ssum_expr  = e; }

let constr bvs is_eq sp =
  { constr_bvars = bvs;
    constr_is_eq = is_eq;
    constr_spoly = sp }

let spoly_of_smonom sas = 
  { sum = [ (BI.one, ssum [] { prod = sas }) ] }

(* ----------------------------------------------------------------------- *)
(* arithmetic operations *)

let negate_sum s =
  L.map ~f:(fun (bi,ssum) -> (BI.(bi *! of_int (-1)), ssum)) s

let minus_spoly s1 s2 =
  let sum2 = negate_sum s2.sum in
  { sum = s1.sum @ sum2 }

let add_spoly s1 s2 =
  { sum = s1.sum @ s2.sum }


let mult_spoly _s1 _s2 =
  failwith "undefined"

module SP = struct
  let ( *! ) a b = mult_spoly a b
  let ( +! ) a b = add_spoly a b
  let ( -! ) a b = minus_spoly a b
  let zero = { sum = [] }
  let one = spoly_of_smonom []
end

(* ----------------------------------------------------------------------- *)
(* useful functions *)

let subst_idx (_c : constr) (_i : ivar) (_j : ivar) =
  failwith "undefined"

let subst (_c : constr) (_p : param) =
  failwith "undefined"

let split (_iv : ivar) (_c : constr) =
  failwith "undefined"

(* ----------------------------------------------------------------------- *)
(* pretty printing *)

let pp_ivar = pp_string

let pp_name_idx fmt (s,i) =
  F.fprintf fmt "%s_[%a]" s pp_ivar i

let pp_name_oidx fmt (s,oi) =
  match oi with
  | None   -> pp_string fmt s
  | Some i -> pp_name_idx fmt (s,i)

let pp_rvar = pp_name_oidx

let pp_param = pp_name_oidx

let pp_hvar = pp_name_idx

let pp_inv fmt = function
  | NoInv -> pp_string fmt ""
  | Inv   -> pp_string fmt "^-1"

let pp_satom fmt = function
  | ARvar(rv,inv) -> F.fprintf fmt "%a%a" pp_rvar rv pp_inv inv
  | AParam(p)     -> F.fprintf fmt "%a" pp_param p
  | AHvar(hv)     -> F.fprintf fmt "%a" pp_hvar hv

let pp_smonom fmt smon =
  F.fprintf fmt "@[<hv 2>%a@]" (pp_list "*" pp_satom) smon.prod

let pp_binder s fmt vars =
  if vars = []
  then pp_string fmt ""
  else F.fprintf fmt "%s %a: " s (pp_list "," pp_ivar) vars

let pp_ssum fmt ssum =
  F.fprintf fmt "@[<hov 2>%a%a@]"
    (pp_binder "sum") ssum.ssum_bvar
    pp_smonom ssum.ssum_expr

let pp_sterm fmt (bi,ssum) =
  if BI.is_one bi then
    pp_ssum fmt ssum
  else
    F.fprintf fmt "@[<hov 2>%s*%a@]" (string_of_big_int bi) pp_ssum ssum
  
let pp_spoly fmt { sum } =
  match L.partition_tf ~f:(fun (bi,_) -> BI.(cmp bi zero >= 0)) sum with
  | [], [] -> 
    F.fprintf fmt "0"
  | [], negs ->
    F.fprintf fmt "@[<hov 2>-(%a)@]" (pp_list "@ + " pp_sterm) (negate_sum negs)
  | pos,[] ->
    F.fprintf fmt "@[<hov 2>-(%a)@]" (pp_list "@ + " pp_sterm) pos
  | pos,negs ->
    F.fprintf fmt "@[<hov 2>%a@ - %a@]"
      (pp_list "@ + " pp_sterm) pos
      (pp_list "@ - " pp_sterm) (negate_sum negs)

let is_eq_to_string = function
  | Eq   -> "="
  | InEq -> "<>"

let pp_constr fmt { constr_bvars = bvs; constr_spoly = sp; constr_is_eq = is_eq } =
  F.fprintf fmt "@[<hv 2>%a%a %s 0@]" (pp_binder "forall") bvs pp_spoly sp (is_eq_to_string is_eq)
