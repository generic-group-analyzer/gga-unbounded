(* * Winning constraint utility functions *)

(* ** Imports *)

open Core_kernel.Std
open Util
open Abbrevs
open Watom
open Wconstrs

(* ** Pretty printing *)

let pp_gname fmt = function
  | G1 -> pp_string fmt "G1"
  | G2 -> pp_string fmt "G2"

let pp_ivar fmt { name; id } =
  if (id = 0) then F.fprintf fmt "%s" name
  else F.fprintf fmt "%s'%d" name id

let pp_name_idx fmt (s,i) =
  F.fprintf fmt "%s_%a" s pp_ivar i

let pp_name_oidx fmt (s,oi) =
  match oi with
  | None   -> pp_string fmt s
  | Some i -> pp_name_idx fmt (s,i)

let pp_rvar = pp_name_oidx
let pp_param = pp_name_oidx

let pp_hvar fmt { hv_name=s; hv_ivar=i; hv_gname=gn } =
  F.fprintf fmt "%s_%a^%a" s pp_ivar i pp_gname gn

let pp_atom fmt = function
  | Uvar(vi)  -> F.fprintf fmt "%a" pp_rvar vi
  | Param(vi) -> F.fprintf fmt "%a" pp_param vi
  | Hvar(hv)  -> F.fprintf fmt "%a" pp_hvar hv

let pp_atom_pow fmt (a,e) =
  if BI.is_one e then
    pp_atom fmt a
  else
    F.fprintf fmt "%a^%s" pp_atom a (BI.to_string e)

let pp_monom fmt mon =
  if (Map.to_alist mon.monom_map)<>[] then
    F.fprintf fmt "%a" (pp_list "*" pp_atom_pow) (Map.to_alist mon.monom_map)
  else
    F.fprintf fmt "1"

let pp_coeff fmt coeff =
  F.fprintf fmt "Coeff_{%a}(%a)" pp_monom (umon2mon coeff.coeff_unif) pp_monom coeff.coeff_mon

let pp_summand fmt summand = 
  match summand with
  | Mon(mon) -> pp_monom fmt mon
  | Coeff(coeff) -> pp_coeff fmt coeff

let pp_varsK fmt ivarsK =
  let pp_ivar_set fmt = function
    | (i, [])  -> F.fprintf fmt "%a" pp_ivar i
    | (i,list) -> F.fprintf fmt "%a <> {%a}" pp_ivar i (pp_list "," pp_ivar) list
  in
  F.fprintf fmt "%a" (pp_list "," pp_ivar_set) (L.map ivarsK ~f:(fun (i,s) -> (i, Set.to_list s)))

let pp_sum fmt sum =
  if sum.sum_ivarsK = [] then
    F.fprintf fmt "%a" pp_summand sum.sum_summand
  else
    F.fprintf fmt "(sum %a: %a)" pp_varsK sum.sum_ivarsK pp_summand sum.sum_summand

let pp_term fmt (s,c) =
  let one = mk_sum [] (Mon(mk_monom [])) in
  if BI.is_one c then pp_sum fmt s
  else if Sum.(compare s one) = 0 then F.fprintf fmt "%s" (BI.to_string c)
  else F.fprintf fmt "%s * %a" (BI.to_string c) pp_sum s

let pp_poly fmt poly =
  let mneg = Map.filter_map poly.poly_map
    ~f:(fun bi -> if BI.(compare bi zero < 0) then Some (BI.opp bi) else None)
  in
  let mpos = Map.filter poly.poly_map ~f:(fun ~key:_k ~data:bi -> BI.(compare bi zero >= 0)) in
  match Map.to_alist mpos, Map.to_alist mneg with
  | [], [] ->
    F.fprintf fmt "0"
  | [], negs ->
    F.fprintf fmt "-(%a)" (pp_list " + " pp_term) negs
  | pos,[] ->
    F.fprintf fmt "%a" (pp_list " + " pp_term) pos
  | pos,negs ->
    F.fprintf fmt "%a - %a"
      (pp_list " + " pp_term) pos
      (pp_list " - " pp_term) negs

let is_eq_to_string = function
  | Eq   -> "="
  | InEq -> "<>"

let pp_constr fmt { constr_ivarsK = qvarsK; constr_poly = p; constr_is_eq = is_eq } =
  if qvarsK <> [] then
    F.fprintf fmt "forall %a. %a %s 0"
               pp_varsK qvarsK
               pp_poly p
              (is_eq_to_string is_eq)
  else
    F.fprintf fmt "%a %s 0" pp_poly p (is_eq_to_string is_eq)

let pp_conj fmt conj =
  let rec aux n list f =
    match list with
    | [] -> F.fprintf f ""
    | c :: rest ->
       F.fprintf f "  %s. %a\n" (string_of_int n) pp_constr c;
       F.fprintf f "%t" (aux (n+1) rest)
  in
  let () =
    if (L.length conj.conj_ivarsK > 0) then
      F.fprintf fmt "exists %a.\n"
        pp_varsK conj.conj_ivarsK
    else ()
  in
  aux 1 conj.conj_constrs fmt
