open Core
open Abbrevs

(* ======================================================================= *)
(* Big int helper functions *)

module BI = struct
  type t = Bigint.t
  let one = Bigint.one
  let zero = Bigint.zero
  let is_one = Bigint.equal one
  let is_zero = Bigint.equal zero
  let opp = Bigint.( ~- )
  let ( *! ) = Bigint.( * )
  let ( +! ) = Bigint.( + )
  let ( -! ) = Bigint.( - )
  let ( /! ) = Bigint.( / )
  let of_int = Bigint.of_int
  let to_int = Bigint.to_int_exn
  let to_string = Bigint.to_string
  let of_string = Bigint.of_string
  let t_of_sexp = Bigint.t_of_sexp
  let sexp_of_t = Bigint.sexp_of_t
  let compare = Bigint.compare
  let equal = Bigint.equal
  let max = Bigint.max
  let min = Bigint.min
  let abs = Bigint.abs
  let rec gcd a b =
    if is_zero b then a
    else gcd b (Bigint.rem a b)
  let sign bi = match Bigint.sign bi with
    | Neg -> -1
    | Zero -> 0
    | Pos -> 1
  let hash_fold_t = Bigint.hash_fold_t
end

(* ======================================================================= *)
(* List functions *)

let unzip1 list =
  let (list1,_) = L.unzip list in
  list1

let unzip2 list =
  let (_,list2) = L.unzip list in
  list2

let repeat_element x n =
  let rec aux output k =
    if k <= 0 then output
    else aux (x :: output) (k-1)
  in
  aux [] n

let rec stringlist2string = function
  | [] -> ""
  | a :: [] -> a
  | a :: rest -> a ^ "," ^ (stringlist2string rest)

let rec dedup_preserve_order ~equal = function
  | [] -> []
  | a :: rest ->
    if L.mem rest a ~equal then dedup_preserve_order ~equal rest
    else a :: (dedup_preserve_order ~equal rest)  

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
  |> L.filter ~f:(fun l -> L.length (L.dedup_and_sort ~compare l) = L.length l)

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
    | a :: rest -> aux (BI.gcd gcd a) rest
  in
  match list with
  | [] -> BI.one
  | hd :: [] -> hd
  | hd :: tl -> aux hd tl

let most_frequent_sign list =
  let positive = L.count list ~f:(fun x -> Stdlib.compare x BI.zero > 0) in
  if (2 * positive) >= L.length list then BI.one
  else BI.(opp one)

let rec before_in_list ~equal i j = function
  | [] -> false
  | a :: rest ->
    if (equal a i) then L.mem rest j ~equal
    else if (equal a j) then false
    else before_in_list ~equal i j rest

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

let cross_lists list1 list2 =
  let rec aux output = function
    | [] -> output
    | a :: rest -> aux (output @ (L.map list2 ~f:(fun b -> (a,b)))) rest
  in
  aux [] list1

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

let fsprintf fstring =
  let buf  = Buffer.create 127 in
  let fmt = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fmt ();
      (Buffer.contents buf))
    fmt fstring

let group rel xs =
  let rec go xs y acc = match xs with
    | []                 -> [ L.rev acc ]
    | x::xs when rel x y -> go xs y (x::acc)
    | x::xs              -> (L.rev acc)::go xs x [x]
  in
  match xs with
  | []    -> []
  | x::xs -> go xs x [x]

let sorted_nub compare xs =
  xs |> L.sort ~compare |> group (fun a b -> compare a b = 0) |> L.map ~f:L.hd_exn

let conc_map f xs = L.concat (L.map ~f xs)

let (%) f g x = f (g x)

let print_messages indent_level msgs =
  L.iter msgs ~f:(fun m -> F.printf "%s%s" (String.make indent_level ' ') m);
  F.print_flush()


(* ======================================================================= *)
(* Map functions *)

let map_add_ignore_duplicate ~key ~data m =
  match Map.add m ~key ~data with
  | `Ok m -> m
  | `Duplicate -> m
