(* * Pretty printing in LaTeX *)

(* ** Imports *)

open Core
open Util
open Abbrevs
open Watom
open Wconstrs

(* ** Printing *)

let pp_gname_latex fmt = function
  | G1 -> pp_string fmt "\\mathbb{G}_{1}"
  | G2 -> pp_string fmt "\\mathbb{G}_{2}"

let pp_ivar_latex fmt { name; id } =
  if (id = 0) then F.fprintf fmt "%s" name
  else F.fprintf fmt "%s_{%s}" name (string_of_int id)

let pp_name_idx_latex fmt (s,i) =
  F.fprintf fmt "%s_{%a}" s pp_ivar_latex i

let pp_name_oidx_latex fmt (s,oi) =
  match oi with
  | None   -> pp_string fmt s
  | Some i -> pp_name_idx_latex fmt (s,i)

let pp_rvar_latex = pp_name_oidx_latex

let pp_param_latex = pp_name_oidx_latex

let pp_hvar_latex fmt { hv_name=s; hv_ivar=i; hv_gname=gn } =
  F.fprintf fmt "%s_{%a}^{%a}" s pp_ivar_latex i pp_gname_latex gn

let pp_atom_latex fmt = function
  | Uvar(vi)  -> F.fprintf fmt "%a" pp_rvar_latex vi
  | Param(vi) -> F.fprintf fmt "%a" pp_param_latex vi
  | Hvar(hv)  -> F.fprintf fmt "%a" pp_hvar_latex hv

let pp_atom_pow_latex fmt (a,e) =
  if BI.is_one e then
    pp_atom_latex fmt a
  else
    F.fprintf fmt "{%a}^{%s}" pp_atom_latex a (BI.to_string e)

let pp_monom_latex fmt mon =
  if not (L.is_empty (Map.to_alist mon.monom_map)) then
    F.fprintf fmt "%a" (pp_list "\\cdot " pp_atom_pow_latex) (Map.to_alist mon.monom_map)
  else
    F.fprintf fmt "1"

let pp_coeff_latex fmt coeff =
  F.fprintf fmt "Coeff_{%a}(%a)" pp_monom_latex (umon2mon coeff.coeff_unif) pp_monom_latex coeff.coeff_mon

let pp_summand_latex fmt summand = 
  match summand with
  | Mon(mon) -> pp_monom_latex fmt mon
  | Coeff(coeff) -> pp_coeff_latex fmt coeff

let pp_varsK_latex fmt ivarsK =
  let pp_ivar_set fmt = function
    | (i, [])  -> F.fprintf fmt "%a" pp_ivar_latex i
    | (i,list) -> F.fprintf fmt "%a \\not \\in \\{%a\\}" pp_ivar_latex i (pp_list "," pp_ivar_latex) list
  in
  F.fprintf fmt "%a" (pp_list "," pp_ivar_set) (L.map ivarsK ~f:(fun (i,s) -> (i, Set.to_list s)))

let pp_sum_latex fmt sum =
  if L.is_empty sum.sum_ivarsK then
    F.fprintf fmt "%a" pp_summand_latex sum.sum_summand
  else
    F.fprintf fmt "\\sum_{%a}\\left(%a\\right)" pp_varsK_latex sum.sum_ivarsK pp_summand_latex sum.sum_summand

let pp_term_latex fmt (s,c) =
  let one = mk_sum [] (Mon(mk_monom [])) in
  if BI.is_one c then pp_sum_latex fmt s
  else if Sum.(compare s one) = 0 then F.fprintf fmt "%s" (BI.to_string c)
  else F.fprintf fmt "%s \\cdot %a" (BI.to_string c) pp_sum_latex s

let pp_poly_latex fmt poly =
  let mneg = Map.filter_map poly.poly_map
    ~f:(fun bi -> if BI.(compare bi zero < 0) then Some (BI.opp bi) else None)
  in
  let mpos = Map.filter poly.poly_map ~f:(fun bi -> BI.(compare bi zero >= 0)) in
  match Map.to_alist mpos, Map.to_alist mneg with
  | [], [] ->
    F.fprintf fmt "0"
  | [], negs when L.length negs > 1 ->
    F.fprintf fmt "-\\left(%a\\right)" (pp_list " + " pp_term_latex) negs
  | pos,[] ->
    F.fprintf fmt "%a" (pp_list " + " pp_term_latex) pos
  | pos,negs ->
    F.fprintf fmt "%a - %a"
      (pp_list " + " pp_term_latex) pos
      (pp_list " - " pp_term_latex) negs

let is_eq_to_string_latex = function
  | Eq   -> "="
  | InEq -> "\\neq "

let pp_constr_latex fmt { constr_ivarsK = qvarsK; constr_poly = p; constr_is_eq = is_eq } =
  if not (L.is_empty qvarsK) then
    F.fprintf fmt "\\forall_{%a}. \\ %a %s 0"
               pp_varsK_latex qvarsK
               pp_poly_latex p
              (is_eq_to_string_latex is_eq)
  else
    F.fprintf fmt "%a %s 0" pp_poly_latex p (is_eq_to_string_latex is_eq)

let pp_conj_latex fmt conj =
  let rec aux n list f =
    match list with
    | [] -> F.fprintf f ""
    | c :: rest ->
       F.fprintf f "<p><script type=\"math/tex\" mode=\"display\">\n%s. \\ \\ %a \n</script></p>\n"
         (string_of_int n) pp_constr_latex c;
       F.fprintf f "%t" (aux (n+1) rest)
  in
  let () =
    if (L.length conj.conj_ivarsK > 0) then
      F.fprintf fmt "<p><script type=\"math/tex\" mode=\"display\">\n \\exists \\ %a.\n</script></p>\n"
        pp_varsK_latex conj.conj_ivarsK
    else ()
  in
  aux 1 conj.conj_constrs fmt
