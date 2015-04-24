open Core.Std
open Big_int

(* ----------------------------------------------------------------------- *)

let big_int_of_sexp se = big_int_of_string (string_of_sexp se)

let sexp_of_big_int bi = sexp_of_string (string_of_big_int bi)

(* ----------------------------------------------------------------------- *)

(* index variables *)
type ivar = string with compare, sexp

(* name with optional index *)
type name_oidx = string * ivar option with compare, sexp

(* name with index *)
type name_idx = string * ivar with compare, sexp

type rvar = name_oidx with compare, sexp

type param = name_oidx with compare, sexp

type hvar = name_idx with compare, sexp

type inv = NoInv | Inv with compare, sexp

type satom =
  | ARvar  of rvar * inv
  | AParam of param
  | AHvar  of hvar
  with compare, sexp

type smonom = { prod : satom list }
  with compare, sexp

type ssum =
  { ssum_coeff : big_int;
    ssum_bvar  : ivar list;
    ssum_expr  : smonom;
  }
  with compare, sexp

(* symbolic polynomial, contains \Sum *)
type spoly = { sum : ssum list }
  with compare, sexp

(* all-constraint in paper *)
type constr =
  { constr_bvars : ivar list;
    constr_expr  : spoly;
    constr_is_eq : bool;
  }
  with compare, sexp

(* ----------------------------------------------------------------------- *)
(* pretty printing *)

(* ----------------------------------------------------------------------- *)
(* constructor functions *)

let rvar ?inv:(inv=NoInv) name = ARvar ((name,None),inv)

let rvar_idx ?inv:(inv=NoInv) name idx = ARvar ((name,Some idx),inv)

let param name = AParam (name,None)

let param_idx name idx = AParam (name,Some idx)

let hvar name idx = AHvar (name,idx)

let ssum coeff bvs e =
  { ssum_coeff = big_int_of_int coeff;
    ssum_bvar  = bvs;
    ssum_expr  = e;
  }

(* ----------------------------------------------------------------------- *)
(* useful functions *)

let subst_idx (_c : constr) (_i : ivar) (_j : ivar) =
  failwith "undefined"

let subst (_c : constr) (_p : param) =
  failwith "undefined"

let split (_iv : ivar) (_c : constr) =
  failwith "undefined"
