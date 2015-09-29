open Core_kernel.Std
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
  let ( /! ) a b = div_big_int a b
  let of_int = big_int_of_int
  let to_string = string_of_big_int
  let t_of_sexp se = big_int_of_string (string_of_sexp se)
  let sexp_of_t bi = sexp_of_string (string_of_big_int bi)
  let compare = compare_big_int
  let equal a b = compare a b = 0
  let max = max_big_int
  let min = min_big_int
  let abs = abs_big_int
  let sign = sign_big_int
end

(* ======================================================================= *)
(* List functions *)

let repeat_element x n =
  let rec aux output k =
    if k <= 0 then output
    else aux (x :: output) (k-1)
  in
  aux [] n

(* insert x at all positions into a list *)
let rec insert x list =
  match list with
  | [] -> [[x]]
  | hd::tl -> (x::list) :: (L.map ~f:(fun l -> hd::l) (insert x tl))

(* Given a list of elements and a number k < list.length, returns all the possible
 sublists of k elements from the list (the order matters) *)
let nchoosek_perm list k ~compare =
    let rec aux output list k =
    if k = 0 then output
    else
      aux (L.concat ( L.map output ~f:(fun l -> L.map list ~f:(fun x -> x::l) ) )) list (k-1)
  in
  aux [[]] list k
  |> L.filter ~f:(fun l -> L.length (L.dedup ~compare l) = L.length l)

(* list of all permutations of a list *)
let rec perms = function
  | [] -> [[]]
  | hd::tl -> L.concat (L.map ~f:(insert hd) (perms tl))   

(* remove one element for every position of a list *)
let rec rm_diagonal = function
  | [] -> []
  | hd::tl -> tl :: (L.map ~f:(fun l -> hd::l) (rm_diagonal tl))

let gcd_big_int_list list =
  let rec aux gcd = function
    | [] -> gcd
    | a :: rest -> aux (gcd_big_int gcd a) rest
  in
  match list with
  | [] -> BI.one
  | hd :: [] -> hd
  | hd :: tl -> aux hd tl

let most_frequent_sign list =
  let positive = L.count list ~f:(fun x -> compare x BI.zero > 0) in
  if (2 * positive) >= L.length list then BI.one
  else BI.(opp one)

let list_map_nth list n f =
  let rec aux hd k = function
    | [] -> failwith "list_map_nth: n is greater than list length"
    | a :: tl ->
       if (k = 1) then hd @ [f a] @ tl
       else aux (hd @ [a]) (k-1) tl
  in
  if n > 0 then aux [] n list
  else failwith "list_map_nth: n has to be positive"

let list_remove list n =
  let rec aux hd k = function
    | [] -> failwith "list_remove: n is greater than list length"
    | a :: tl ->
       if (k = 1) then hd @ tl
       else aux (hd @ [a]) (k-1) tl
  in
  if n > 0 then aux [] n list
  else failwith "list_remove: n has to be positive"

let range n m =
  let rec aux output k = if (k <= m) then aux (output @ [k]) (k+1) else output in
  if (n <= m) then aux [] n
  else []

let rec unique xs ~equal =
  match xs with
  | y::ys -> if L.mem ~equal ys y then false else unique ys ~equal
  | []    -> true

let list2multiplicity list ~equal =
  let distinct a b = not (equal a b) in
  let rec aux output = function
    | [] -> output
    | a :: rest -> aux ((a, 1+(L.count rest ~f:(equal a))) :: output)
                       (L.filter rest ~f:(distinct a))
  in
  aux [] list
        
let repeat_string s n =
  let rec aux output k =
    if (k = 0) then output
    else aux (output ^ s) (k-1)
  in
  if (n > 0) then aux "" n
  else ""

(* Take first n elements in a list *)
let first_n list n =
  let rec aux output k = function
    | [] -> output
    | a :: rest -> if (k = 0) then output
                   else aux (output @ [a]) (k-1) rest
  in
  aux [] n list
            
let sub_list list1 list2 ~equal =
  L.fold_left list1
     ~init:true
     ~f:(fun b a -> b && (L.mem list2 a ~equal))

let partition_double gt list aux_list =
  let rec aux left right aux_left aux_right list aux_list =
    match list, aux_list with
    | ([],[]) -> left, right, aux_left, aux_right
    | (x::xs, u::us) ->
       if (gt x) then aux left (right @ [x]) aux_left (aux_right @ [u]) xs us
       else aux (left @ [x]) right (aux_left @ [u]) aux_right xs us
    | _ -> failwith "lists must have the same length"
  in
  aux [] [] [] [] list aux_list

let rec quicksort_double gt list aux_list =
  match list, aux_list with
  | ([],[]) -> ([],[])
  | (x::xs, u::us) ->
      let ys, zs, vs, ws = partition_double (gt x) xs us in
      let s1, aux_s1 = quicksort_double gt ys vs in
      let s2, aux_s2 = quicksort_double gt zs ws in
      s1 @ [x] @ s2, aux_s1 @ [u] @ aux_s2      
  | _ -> failwith "lists must have the same length"

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

let group rel xs =
  let rec go xs y acc = match xs with
    | []                 -> [ L.rev acc ]
    | x::xs when rel x y -> go xs y (x::acc)
    | x::xs              -> (L.rev acc)::go xs x [x] 
  in
  match xs with
  | []    -> []
  | x::xs -> go xs x [x]

let sorted_nub cmp xs =
  xs |> L.sort ~cmp |> group (fun a b -> cmp a b = 0) |> L.map ~f:L.hd_exn

let conc_map f xs = L.concat (L.map ~f xs)

let (%) f g x = f (g x)
