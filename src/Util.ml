open Core.Std
open Abbrevs
open Big_int

(* ======================================================================= *)
(* Big int helper functions *)

module BI = struct
  type t = big_int
  let one = unit_big_int
  let zero = zero_big_int
  let is_one = eq_big_int one
  let is_zero = eq_big_int zero
  let opp = minus_big_int	      
  let ( *! ) a b = mult_big_int a b
  let ( +! ) a b = add_big_int a b
  let ( -! ) a b = a +! (opp b)
  let of_int = big_int_of_int
  let to_string = string_of_big_int
  let t_of_sexp se = big_int_of_string (string_of_sexp se)
  let sexp_of_t bi = sexp_of_string (string_of_big_int bi)
  let compare = compare_big_int
  let equal a b = compare a b = 0
end

(* ======================================================================= *)
(* Pretty printing *)

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> F.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let pp_list_c pe = (pp_list "," pe)
let pp_list_s = pp_list_c (fun fmt -> F.fprintf fmt "%s")

let pp_opt pp fmt o =
  match o with
  | Some x -> pp fmt x
  | None    -> F.fprintf fmt "--"

let pp_around before after pp fmt x =
  F.fprintf fmt "%s%a%s" before pp x after

let pp_string fmt s = F.fprintf fmt "%s" s

let pp_int fmt i = F.fprintf fmt "%i" i

let pp_if c pp1 pp2 fmt x =
  if c then pp1 fmt x else pp2 fmt x

let pp_pair pp1 pp2 fmt (a,b) =
  F.fprintf fmt "(%a,%a)" pp1 a pp2 b

let fsprintf fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      (Buffer.contents buf))
    fbuf fmt
