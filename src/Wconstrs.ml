open Core.Std
open Util
open Abbrevs
open Watom

(* ======================================================================= *)
(* constraint expressions and constraints  *)

type is_eq = Eq | InEq with compare, sexp

(* Mapping from atom to exponent, we ensure in mk_monom that only random
   variables can have negative exponents *)
type monom = BI.t Atom.Map.t with compare, sexp

(* [Sum ivars: monom] where monom can contain bound and free index variables *)
type sum = {
  ivars  : ivar list;
  i_ineq : ivar_pair list;
  monom  : monom;
} with compare, sexp
		  
(* data structures with sums *)
module Sum = struct
  module T = struct
    type t = sum
    let compare = compare_sum
    let sexp_of_t = sexp_of_sum
    let t_of_sexp = sum_of_sexp
  end
  include T
  include Comparable.Make(T)
end

(* Mapping from term to coefficient, we ensure in mk_poly
   that coefficients cannot be zero *)
type poly = BI.t Sum.Map.t with compare, sexp

(* all-constraint in paper *)
type constr = {
  qvars  : ivar list;
  q_ineq  : ivar_pair list;
  is_eq  : is_eq;
  poly   : poly;
} with compare, sexp

(* constraint conjunction *)
type constr_conj = constr list with compare, sexp

type constr_disj = constr_conj list with compare, sexp

(* ----------------------------------------------------------------------- *)
(* equality functions *)

let equal_is_eq a b = compare_is_eq a b = 0
let equal_monom a b = compare_monom a b = 0
let equal_sum a b = compare_sum a b = 0
let equal_poly a b = compare_poly a b = 0
let equal_constr a b = compare_constr a b = 0
let equal_constr_conj a b = compare_constr_conj a b = 0
let equal_constr_disj a b = compare_constr_disj a b = 0
  
(* ----------------------------------------------------------------------- *)
(* variable occurences *)

let ivars_monom mon =
  Map.fold mon
    ~init:Ivar.Set.empty
    ~f:(fun ~key:k ~data:_v se -> Set.union se (ivars_atom k))

let ivars_sum sum =
  ivars_monom sum.monom

let ivars_poly poly =
  L.fold_left (Map.keys poly)
    ~init:Ivar.Set.empty
    ~f:(fun se1 t -> Set.union se1 (ivars_sum t))

let ivars_constr constr =
  ivars_poly constr.poly

let ivars_conj conj =
  L.fold_left conj ~init:Ivar.Set.empty
	           ~f:(fun se1 t -> Set.union se1 (ivars_constr t))

let new_ivar taken old_idx =
  let n = old_idx.name in
  let rec go i =
    let idx = { name = n; id = i } in
    if Set.mem taken idx then
      go (i+1)
    else
      idx
  in
  go 0

let renaming_away_from taken ivars =
  Set.fold ivars ~init:(Ivar.Map.empty,taken)
    ~f:(fun (m,taken) ivar ->
          let ivar' = new_ivar taken ivar in
          (Map.add m ~key:ivar ~data:ivar', Set.add taken ivar'))

let apply_renaming rn ivar =
  Option.value ~default:ivar (Map.find rn ivar)

let free_ivars_sum s =
  (Set.diff (ivars_sum s) (Ivar.Set.of_list s.ivars))

let bound_ivars_sum s =
  (Set.inter (ivars_sum s) (Ivar.Set.of_list s.ivars))

let free_ivars_poly p =
  Map.fold p 
    ~init:Ivar.Set.empty
    ~f:(fun ~key:s ~data:_c se -> Set.union se (free_ivars_sum s))

let bound_ivars_poly p =
  Map.fold p 
    ~init:Ivar.Set.empty
    ~f:(fun ~key:s ~data:_c se -> Set.union se (bound_ivars_sum s))  

let cartesian l l' = 
  List.concat (List.map ~f:(fun e -> List.map ~f:(fun e' -> (e,e')) l') l)

let all_pairs (ivars : ivar list) =
  L.filter (cartesian ivars ivars) ~f:(fun (x,y) -> x <> y)
  |> Ivar_Pair.Set.of_list       
  |> Ivar_Pair.Set.to_list

let all_ivar_distinct membership update_t rename ivars_t t =
  let rec do_split x = function
    | [] -> [x]
    | (i,j) :: rest_pairs ->
       if membership x (i,j) then do_split x rest_pairs
       else
	 let ts1 = do_split (update_t x (i,j)) rest_pairs in
	 let ts2 = do_split (rename x i j) (all_pairs (ivars_t x)) in
	 ts1 @ ts2
  in
  do_split t (all_pairs (ivars_t t))
    
(* ----------------------------------------------------------------------- *)
(* smart constructors *)

let mult_monom_atom m (e,a) =
    if BI.compare e BI.zero < 0 && not (is_rvar a) then
      failwith "mult_monom_atom: only random variables can have negative exponent";
    Map.change m a
      (function 
         | None   -> Some e
         | Some i -> 
           let i = BI.(i +! e) in
           if BI.is_zero i then None else Some i)

let mk_monom atoms =
  L.fold_left atoms
    ~init:Atom.Map.empty
    ~f:(fun m (inv,a) -> mult_monom_atom m (bi_of_inv inv,a))

let mk_sum ivs ivs_dist mon =
  let ivs_dist = L.filter ivs_dist ~f:(fun (x,y) -> L.mem ivs x && L.mem ivs y) in
  let ivar_pairs = Ivar_Pair.Set.to_list (Ivar_Pair.Set.of_list ivs_dist) in
  let ivs = Ivar.Set.to_list (Ivar.Set.of_list ivs) in
  { ivars = ivs; i_ineq = ivar_pairs; monom = mon }

let add_poly_term m (c,t) =
  Map.change m t
    (function 
    | None    -> Some c
    | Some c' ->
      let c = BI.(c +! c') in
      if BI.is_zero c then None else Some c)
    
let map_idx_monom ~f m =
  Atom.Map.fold m
    ~init:Atom.Map.empty
    ~f:(fun ~key:a ~data:bi m -> mult_monom_atom m (bi,Watom.map_idx ~f a))

let all_ivar_distinct_poly p =
  let membership s (i,j) = L.mem s.i_ineq (i,j) || L.mem s.i_ineq (j,i) in
  let update s pair = mk_sum s.ivars (pair::s.i_ineq) s.monom in
  let rename s i j =
    let f = (fun x -> if x = i then j else x) in
    mk_sum (L.map s.ivars ~f) (L.map s.i_ineq ~f:(fun (x,y) -> (f x, f y))) (map_idx_monom s.monom ~f)
  in
  let ivars_t s = s.ivars in
  Map.fold p
    ~init:Sum.Map.empty
    ~f:(fun ~key:s ~data:c p' ->
	L.fold_left (L.map (all_ivar_distinct membership update rename ivars_t s) ~f:(fun x -> (c,x)) )
    	  ~init:p'
      	  ~f:add_poly_term)
    
let mk_poly terms =
  L.fold_left ~init:Sum.Map.empty ~f:add_poly_term terms |> all_ivar_distinct_poly
							      
let mk_constr ivs ivs_dist is_eq poly =
  let iv_occs = ivars_poly poly in
  let ivs = L.filter ~f:(fun iv -> Set.mem iv_occs iv) ivs in
  let ivs = Ivar.Set.to_list (Ivar.Set.of_list ivs) in
  let ivs_dist = L.filter ivs_dist ~f:(fun (x,y) -> L.mem ivs x && L.mem ivs y) in
  let ivar_pairs = Ivar_Pair.Set.to_list (Ivar_Pair.Set.of_list ivs_dist) in
  { qvars = ivs; q_ineq = ivar_pairs; is_eq = is_eq; poly = poly }

(* ----------------------------------------------------------------------- *)
(* arithmetic operations *)

let opp_poly p =
  Map.map ~f:(fun coeff -> BI.opp coeff) p

let add_poly p1 p2 =
  let add_term ~key:_k = function
    | `Both(c1,c2) ->
      BI.(
        let c = c1 +! c2 in
        if is_zero c then None else Some c)
    | `Left c | `Right c -> if BI.is_zero c then None else Some c
  in
  Map.merge p1 p2 ~f:add_term

let minus_poly p1 p2 =
  add_poly p1 (opp_poly p2)

let mult_monom m1 m2 =
  let add_exp ~key:_k = function
    | `Both(e1,e2) ->
      BI.(
        let e = e1 +! e2 in
        if is_zero e then None else Some e)
    | `Left e | `Right e -> Some e
  in
  Map.merge m1 m2 ~f:add_exp
   	    
let mult_sum s1 s2 =
  let free_vars = Set.union (free_ivars_sum s1) (free_ivars_sum s2) in
  let (rn1,taken) = renaming_away_from free_vars (Ivar.Set.of_list s1.ivars) in
  let ivars1 = L.map s1.ivars ~f:(apply_renaming rn1) in
  let i_ineq1 = L.map s1.i_ineq ~f:(fun (x,y) -> (apply_renaming rn1 x, apply_renaming rn1 y)) in
  let monom1 = map_idx_monom  ~f:(apply_renaming rn1) s1.monom in
  let (rn2,_) = renaming_away_from taken (Ivar.Set.of_list s2.ivars) in
  let ivars2 = L.map s2.ivars ~f:(apply_renaming rn2)in
  let i_ineq2 = L.map s2.i_ineq ~f:(fun (x,y) -> (apply_renaming rn2 x, apply_renaming rn2 y)) in
  let monom2 = map_idx_monom ~f:(apply_renaming rn2) s2.monom in
  mk_sum (ivars1 @ ivars2) (i_ineq1 @ i_ineq2) (mult_monom monom1 monom2)

let mult_term (c1,s1) (c2,s2) =
  (BI.(c1 *! c2), mult_sum s1 s2)

let mult_poly_term p (c0,s0) =
  Map.fold p
    ~init:(mk_poly [])
    ~f:(fun ~key:s ~data:c p ->
          let p' = mk_poly [mult_term (c0,s0) (c,s)] in
          add_poly p p')

let mult_poly p1 p2 =
  Map.fold p1
    ~init:(mk_poly [])
    ~f:(fun ~key:s ~data:c p ->
          let p' = mult_poly_term p2 (c,s) in
          add_poly p p')

let map_idx_poly ~f p =
  Map.fold p
    ~init:Sum.Map.empty
    ~f:(fun ~key:s ~data:c p' -> add_poly p'
       (mk_poly [(c, mk_sum (L.map ~f s.ivars) s.i_ineq (map_idx_monom ~f s.monom))]))

let all_ivar_distinct_constr_conj conj =
  let membership c (i,j) = L.mem c.q_ineq (i,j) || L.mem c.q_ineq (j,i) in
  let update c pair = mk_constr c.qvars (pair::c.q_ineq) c.is_eq c.poly in
  let rename c i j =
    let f = (fun x -> if x = i then j else x) in
    mk_constr (L.map c.qvars ~f) (L.map c.q_ineq ~f:(fun (x,y) -> (f x, f y)))
	      c.is_eq (map_idx_poly ~f c.poly)
  in
  let ivars_t c = c.qvars in
  L.map conj ~f:(all_ivar_distinct membership update rename ivars_t)
  |> L.concat
    
module SP = struct
  let ( *! ) a b = mult_poly a b |> all_ivar_distinct_poly
  let ( +! ) a b = add_poly a b
  let ( -! ) a b = minus_poly a b
  let zero = mk_poly []

  (* define shortcut poly constructors *)
  let of_coeff_monom c m = mk_poly [(c, mk_sum [] [] (mk_monom m))] |> all_ivar_distinct_poly
  let of_const c  = of_coeff_monom c []
  let of_monom m  = of_coeff_monom BI.one m
  let of_a a = of_monom [(NoInv,a)]
  let sum ivs p =
    Map.fold p
      ~init:zero
      ~f:(fun ~key:sum ~data:c new_p ->
            add_poly_term new_p (c,(mk_sum (ivs@sum.ivars) [] sum.monom)))
    |> all_ivar_distinct_poly
  let one = of_const BI.one
end

(* ----------------------------------------------------------------------- *)
(* pretty printing *)

let is_eq_to_string = function
  | Eq   -> "="
  | InEq -> "<>"

let pp_atom_pow fmt (a,e) =
  if BI.is_one e then
    pp_atom fmt a
  else
    F.fprintf fmt "%a^%s" pp_atom a (BI.to_string e)

let pp_monom fmt mon =
  if (Map.to_alist mon)<>[] then
    F.fprintf fmt "@[<hv 2>%a@]"
	      (pp_list " * " pp_atom_pow) (Map.to_alist mon)
  else
    F.fprintf fmt "@[<hv 2>1@]"

let pp_binder s fmt vars =
  if vars = []
  then pp_string fmt ""
  else F.fprintf fmt "%s %a: " s (pp_list "," pp_ivar) vars

let pp_sum fmt sum =
  if sum.ivars<>[] && sum.i_ineq<>[] then 
    F.fprintf fmt "@[<hov 2>(%a(%a) %a)@]"
      (pp_binder "sum") sum.ivars
      (pp_list ", " pp_ivar_pair) sum.i_ineq
      pp_monom sum.monom
  else if sum.ivars <> [] then
      F.fprintf fmt "@[<hov 2>(%a%a)@]"
      (pp_binder "sum") sum.ivars
      pp_monom sum.monom
  else
    F.fprintf fmt "@[<hov 2>%a@]"
      pp_monom sum.monom

let pp_term fmt (s,c) =
  let one = mk_sum [] [] (mk_monom []) in
  if BI.is_one c then pp_sum fmt s
  else if Sum.(compare s one) = 0 then F.fprintf fmt "@[<hov 2>%s@]" (BI.to_string c) 
  else F.fprintf fmt "@[<hov 2>%s * %a@]" (BI.to_string c) pp_sum s

let pp_poly fmt poly =
  let mneg = Map.filter_map poly
    ~f:(fun bi -> if BI.(compare bi zero < 0) then Some (BI.opp bi) else None)
  in
  let mpos = Map.filter poly ~f:(fun ~key:_k ~data:bi -> BI.(compare bi zero >= 0)) in
  match Map.to_alist mpos, Map.to_alist mneg with
  | [], [] ->
    F.fprintf fmt "0"
  | [], negs ->
    F.fprintf fmt "@[<hov 2>-(%a)@]" (pp_list "@ + " pp_term) negs
  | pos,[] ->
    F.fprintf fmt "@[<hov 2>%a@]" (pp_list "@ + " pp_term) pos
  | pos,negs ->
    F.fprintf fmt "@[<hov 2>%a@ - %a@]"
      (pp_list "@ + " pp_term) pos
      (pp_list "@ - " pp_term) negs

let pp_constr fmt { qvars = qvs; q_ineq = qinqs; poly = p; is_eq = is_eq } =
  if qinqs<>[] then
    F.fprintf fmt "@[<hov 2>%a(%a) %a %s 0@]"
	      (pp_binder "forall") qvs
	      (pp_list ", " pp_ivar_pair) qinqs
	       pp_poly p
	      (is_eq_to_string is_eq)
  else
    F.fprintf fmt "@[<hov 2>%a%a %s 0@]" (pp_binder "forall") qvs pp_poly p (is_eq_to_string is_eq)

let pp_constr_conj fmt conj =
  let rec aux n list f =
    match list with
    | [] -> F.fprintf f "\n"
    | c :: rest ->
       F.fprintf f "@[%i: %a@]@\n" n pp_constr c;
       F.fprintf f "%t" (aux (n+1) rest)
  in
  aux 1 conj fmt

(* ----------------------------------------------------------------------- *)	      
(* isomorphic constraints *)
(*
let create_ivars iv_name n =
  let rec aux list k =
    if k = n then List.rev list
    else aux ({name = iv_name; id = k} :: list) (k+1)
  in
  if n >= 0 then aux [] 0
  else failwith "create_ivars: n has to be non-negative"

let rec rename_monom_indices m list = function
  | [] -> m
  | hd :: tl ->
     let hd2 = L.hd_exn list in
     let tl2 = L.tl_exn list in
     rename_monom_indices (map_idx_monom m ~f:(fun i -> if i = hd2 then hd else i)) tl2 tl
  		
let rename_sum_indices p iv_name =
  let aux s =
    let bound_ivars = Set.to_list (bound_ivars_sum s) in
    let new_ivars = create_ivars iv_name (L.length bound_ivars) in
    mk_sum new_ivars (rename_monom_indices s.monom bound_ivars new_ivars)
  in
  Map.fold p
    ~init:(Sum.Map.empty)
    ~f:(fun ~key:s ~data:c p' -> add_poly p' (mk_poly [(c,aux s)]))

let rename_poly_indices p list1 list2 =
  let rec aux p' list'  = function
    | [] -> p'	      
    | hd :: tl ->       
       let hd' = L.hd_exn list' in
       let tl' = L.tl_exn list' in
       aux (map_idx_poly p' ~f:(fun i -> if i = hd' then hd else i)) tl' tl
  in
  let auxiliar_indices = create_ivars "reserved_aux" (L.length list1) in
  aux (aux p list1 auxiliar_indices) auxiliar_indices list2
    
let next_lex_permutation permutation comp lowest =
  let find_first_decrement list =
    let rec aux hd = function
      | [] | _ :: [] -> hd, lowest, []
      | element1 :: element2 :: rest ->
     if comp element1 element2 <= 0 then
       aux (hd @ [element1]) (element2 :: rest)
     else
       (hd @ [element1]), element2, rest
    in
    aux [] list
  in

  let find_first_successor pivot list =   
    let rec aux hd = function
      | [] -> failwith "Impossible to be here"
      | element :: rest ->
     if comp element pivot > 0 then
           hd, element, rest
     else
       aux (hd @ [element]) rest
    in
    aux [] list
  in

  let hd, pivot, tail = find_first_decrement (List.rev permutation) in
  if pivot = lowest then permutation
  else
    let h1, successor, h2 = find_first_successor pivot hd in
    let header = h1 @ [pivot] @ h2 in
    List.rev ((List.rev header) @ [successor] @ tail)
    
let any_permutation list (f : 'a list -> bool) comp lowest=
  let rec aux permutation =
    if (f permutation) then true
    else
      let next_permutation = next_lex_permutation permutation comp lowest in
      if (next_permutation = permutation) then false
      else aux next_permutation
  in
  aux (L.sort ~cmp:comp list)
              
let isomorphic_constr a b =
  let a_poly = rename_sum_indices a.poly "reserved" in
  let b_poly = rename_sum_indices b.poly "reserved" in
  let idx_a = Set.to_list (bound_ivars_poly a.poly) in
  let idx_b = Set.to_list (bound_ivars_poly b.poly) in
  let free_a = Set.to_list (Set.diff (free_ivars_poly a.poly) (Ivar.Set.of_list a.qvars)) in
  let free_b = Set.to_list (Set.diff (free_ivars_poly b.poly) (Ivar.Set.of_list b.qvars)) in
  if (L.length idx_a <> L.length idx_b) || (L.length a.qvars) <> (L.length b.qvars) ||
     (compare_is_eq a.is_eq b.is_eq <> 0) then false
  else
    any_permutation b.qvars
      (fun x -> any_permutation free_b
	  (fun y -> any_permutation idx_b
	      (fun z -> equal_poly a_poly (rename_poly_indices
		                            (rename_poly_indices
				              (rename_poly_indices (b_poly) z idx_a)
				             y free_a)
					   x a.qvars)
	       ) Ivar.compare {name = ""; id = -1}
	  ) Ivar.compare {name = ""; id = -1}
      ) Ivar.compare {name = ""; id = -1}

let isomorphic_poly a b =
  isomorphic_constr (mk_constr [] Eq a) (mk_constr [] Eq b)
 *)
