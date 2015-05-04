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
  is_eq  : is_eq;
  poly   : poly;
} with compare, sexp

(* constraint conjunction *)
type constr_conj = constr list with compare, sexp

type constr_disj = constr_conj list with compare, sexp
		  					    
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

let mk_sum ivs mon = { ivars = ivs; monom = mon }

let poly_add m (c,t) =
  Map.change m t
    (function 
    | None    -> Some c
    | Some c' ->
      let c = BI.(c +! c') in
      if BI.is_zero c then None else Some c)

let mk_poly terms =
  L.fold_left ~init:Sum.Map.empty ~f:poly_add terms

let mk_constr ivs is_eq poly =
  let iv_occs = ivars_poly poly in
  let ivs = L.filter ~f:(fun iv -> Set.mem iv_occs iv) ivs in
  { qvars = ivs; is_eq = is_eq; poly = poly }

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
    | `Left c | `Right c -> Some c
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

let map_idx_monom ~f m =
  Atom.Map.fold m
    ~init:Atom.Map.empty
    ~f:(fun ~key:a ~data:bi m -> mult_monom_atom m (bi,Watom.map_idx ~f a))

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

let rename rn ivar =
  Option.value ~default:ivar (Map.find rn ivar)

let free_vars_sum s =
  (Set.diff (ivars_sum s) (Ivar.Set.of_list s.ivars))

let mult_sum s1 s2 =
  let free_vars = Set.union (free_vars_sum s1) (free_vars_sum s2) in
  let (rn1,taken) = renaming_away_from free_vars (Ivar.Set.of_list s1.ivars) in
  let ivars1 = L.map s1.ivars ~f:(rename rn1) in
  let monom1 = map_idx_monom  ~f:(rename rn1) s1.monom in
  let (rn2,_) = renaming_away_from taken (Ivar.Set.of_list s2.ivars) in
  let ivars2 = L.map s2.ivars ~f:(rename rn2)in
  let monom2 = map_idx_monom ~f:(rename rn2) s2.monom in
  mk_sum (ivars1 @ ivars2) (mult_monom monom1 monom2)

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

module SP = struct
  let ( *! ) a b = mult_poly a b
  let ( +! ) a b = add_poly a b
  let ( -! ) a b = minus_poly a b
  let zero = mk_poly []

  (* define shortcut poly constructors *)
  let of_term c m = mk_poly [(c, mk_sum [] (mk_monom m))]
  let of_const c  = of_term c []
  let of_monom m  = of_term BI.one m
  let of_a a = of_term BI.one [(NoInv,a)]
  let sum ivs p =
    Map.fold p
      ~init:zero
      ~f:(fun ~key:sum ~data:c new_p ->
            poly_add new_p (c,(mk_sum (ivs@sum.ivars) sum.monom)))

  let one = of_const BI.one
end

(* ----------------------------------------------------------------------- *)
(* Extract parameter polynomials from poly *)

type monlist = (atom * BI.t) list with compare

let equal_monlist a b =
  compare_monlist a b = 0

let monom_to_monlist p_var mon =
  Map.filter mon ~f:(fun ~key:k ~data:_v -> p_var k)
  |> Map.to_alist
  |> L.sort ~cmp:(fun (k1,_) (k2,_) -> compare_atom k1 k2)
  
let rvars (mon : monom)  = monom_to_monlist is_rvar mon
let hvars (mon : monom)  = monom_to_monlist is_hvar mon
let params (mon : monom) = monom_to_monlist is_param mon

let monom_filter_vars p_var mon =
  Map.filter ~f:(fun ~key:k ~data:_d -> p_var k) mon

let rvars_monom  (mon : monom) = monom_filter_vars is_rvar mon
let hvars_monom  (mon : monom) = monom_filter_vars is_hvar mon
let params_monom (mon : monom) = monom_filter_vars is_param mon


let coeff_sum (c : BI.t) (s : sum) (mon : monom) =
  if (equal_monlist (rvars s.monom) (rvars mon)) &&
     (equal_monlist (hvars s.monom) (hvars mon))
  then mk_poly [(c, mk_sum s.ivars (params_monom s.monom))]
  else SP.zero
    
let coeff (p : poly) (mon : monom) =
  Map.fold p
    ~init:(mk_poly [])
	  ~f:(fun ~key:s ~data:c p -> add_poly p (coeff_sum c s mon) )

let mons (p : poly) =
  Map.fold p
    ~init:[]
	  ~f:(fun ~key:s ~data:_c list ->
          (Map.filter s.monom ~f:(fun ~key:v ~data:_e -> not (is_param v))) :: list)

let degree (v : atom) (m : monom) =
  Option.value ~default:BI.zero (Map.find m v)

(* ----------------------------------------------------------------------- *)
(* ??? *)


type k_inf = {
  n : monom list  ; (* non-recursive knowledge in G_i *)
  r : monom list  ; (* recursive knowledge in G_i *)
  rj : monom list ; (* recursive indexed knowledge in G_i *)
}

(* ----------------------------------------------------------------------- *)
(* Split: create a new free index variable *)

let subst_idx_sum (s : sum) (i : ivar) (j : ivar) =
  if L.mem s.ivars i then failwith "subst_idx_sum: impossible to substitute a summation variable"
  else mk_sum s.ivars (map_idx_monom ~f:(fun x -> if x = i then j else x) s.monom)
	   
let subst_idx_poly (p : poly) (i : ivar) (j : ivar) =
  Map.fold p
    ~init:(mk_poly [])
	  ~f:(fun ~key:s ~data:c p -> add_poly p (mk_poly [(c, subst_idx_sum s i j)]) )
	   	   
let subst_idx (c : constr) (i : ivar) (j : ivar) =
  { c with
    qvars = L.filter c.qvars ~f:((<>) i);
    poly = subst_idx_poly c.poly i j }

let split_sum (iv : ivar) (c : BI.t) (sum : sum) =
  let rec aux s =    
    match s.ivars with      
    | [] -> [(c,s)]
    | i :: rest_idx ->
       let without_i = { s with ivars = rest_idx } in
       (L.map (aux without_i)
	        ~f:(fun (k,x) -> (k, {x with ivars = i::x.ivars }) ))
       @ (aux (subst_idx_sum without_i i iv))
  in  
  if L.mem sum.ivars iv
  then failwith "split_sum: given index variable must be fresh"
  else aux sum
         
let split_poly (iv : ivar) (p : poly) =
  Map.fold p ~init:(mk_poly [])
	     ~f:(fun ~key:s ~data:c p ->
	         add_poly p (mk_poly (split_sum iv c s)) )
      
let split_constr (iv : ivar) (constr : constr) =
  let rec aux c =	
    match c.qvars with      
    | [] -> [c]
    | i :: rest_idx ->
      let without_i = { c with qvars = rest_idx } in
      (L.map (aux without_i)
	       ~f:(fun x -> { qvars = i :: x.qvars ; is_eq = x.is_eq ; poly = x.poly }))
	    @ (aux (subst_idx without_i i iv) )
  in
  if L.mem constr.qvars iv
  then failwith (fsprintf "split_constr: given index variable %a not fresh" pp_ivar iv)
  else aux  { constr with poly = split_poly iv constr.poly }
       
let split (iv : ivar) (conj : constr_conj) =
  List.concat_map conj ~f:(split_constr iv)

(* ----------------------------------------------------------------------- *)
(* stable terms *)

let mons_sets_product (mlist1 : monom list) (mlist2 : monom list) =
  L.concat_map mlist1 ~f:(fun m1 -> L.map mlist2 ~f:(fun m2 -> mult_monom m1 m2))
  |> L.dedup ~compare:compare_monom

let all_index_poss monom_list indices =
  let all_indices m = L.map indices ~f:(fun x -> map_idx_monom ~f:(fun _ -> x) m) in
  L.concat_map monom_list ~f:all_indices
  |> L.dedup ~compare:compare_monom

let rvars_set (m : monom) =
  Map.fold m
    ~init:Atom.Set.empty
	  ~f:(fun ~key:k ~data:_v se ->
	        Set.union se (if is_rvar k then Atom.Set.singleton k else Atom.Set.empty))
	     
let list2string (strings : string list) sep lim1 lim2 =
  lim1 ^ (String.concat ~sep strings) ^ lim2
	     
let matrix_row (a : atom) (recur : monom list) (recur_j : monom list) =
  list2string (List.map (recur @ recur_j) ~f:(fun x -> BI.to_string (degree a x))) ", " "[" "]"
	     
let smt_case mon rvars_hm nr recur recur_j n_indices =
  let monomials =
    Set.to_list
      (Set.union (rvars_set mon) (Set.union (rvars_set rvars_hm) (rvars_set nr)))
  in
  let (matrix, vector) =
    L.fold_left monomials ~init:([], [])
      ~f:(fun (mat,vec) x ->
	          (mat @ [matrix_row x recur recur_j],
	           vec @ [BI.(to_string ((degree x mon) -! (degree x rvars_hm) -! (degree x nr)))] ) )
  in
  "\'{\\\"matrix\\\" : " ^ (list2string matrix ", " "[" "]") ^
    ", \\\"vector\\\": " ^ (list2string vector ", " "[" "]") ^
    ", \\\"lambda\\\": " ^ (string_of_int (L.length recur)) ^
    ", \\\"indices\\\": " ^ (string_of_int (n_indices)) ^ "}\'"
    
let smt_system mon (rvars_hm : monom) non_recur recur recur_j n_indices =
  L.fold_left non_recur
     ~init:String.Set.empty	      
     ~f:(fun se x ->
           Set.union se
		         (String.Set.singleton (smt_case mon rvars_hm x recur recur_j n_indices)) )     

let simple_system mon rvars_hm n r rj indices =
  let non_recursive = all_index_poss n indices in
  let recursive_j = all_index_poss rj indices in
  let system = smt_system mon rvars_hm non_recursive r recursive_j (L.length indices) in	
  list2string (Set.to_list system) ", " "\"[" "]\""

let double_system mon rvars_hm n1 r1 rj1 n2 r2 rj2 indices =
  let non_recursive1 = all_index_poss n1 indices in  
  let non_recursive2 = all_index_poss n2 indices in
  let non_recursive = mons_sets_product non_recursive1 non_recursive2 in

  let recursive_j1 = all_index_poss rj1 indices in
  let recursive_j2 = all_index_poss rj2 indices in
  let recursive_j = mons_sets_product recursive_j1 recursive_j2 in

  let recursive = mons_sets_product r1 r2 in
  let recursive = recursive @ (L.filter recursive_j
				        ~f:(fun x -> Ivar.Set.is_empty (ivars_monom x)) ) in
  let recursive_j = L.filter recursive_j
			     ~f:(fun x -> not (Ivar.Set.is_empty (ivars_monom x))) in
  let system = smt_system mon rvars_hm non_recursive recursive recursive_j (L.length indices) in
  list2string (Set.to_list system) ", " "\"[" "]\""

let smt_solver system =
  let syscall cmd =
    let ic, oc = Unix.open_process cmd in
    let buf = Buffer.create 16 in
    (try while true do Buffer.add_channel buf ic 1 done
     with End_of_file -> ());
    let _ = Unix.close_process (ic, oc) in Buffer.contents buf
  in
  let result = syscall ("python smt_solver.py " ^ system) in
  match result with
  | "True\n" -> true
  | "False\n" -> false
  | _ -> failwith "Communication with python failed"
    	      
let overlap (m : monom) (hm: monom) (k1 : k_inf) (k2 : k_inf) =
  let indices = Ivar.Set.to_list (ivars_monom (mult_monom m hm)) in
  let handles_list =
    L.concat_map (hvars hm)
	    ~f:(fun (v,e) ->
            let v = match v with Hvar hv -> hv | _ -> assert false in
            if BI.is_one e then [v]
				    else if BI.(equal e (of_int 2)) then [v;v]
					  else failwith "Not supported")
  in
  let system =
    match handles_list with
    | [h] ->
      begin match h.hv_gname with
      | G1 -> simple_system m (rvars_monom hm) k1.n k1.r k1.rj indices
      | G2 -> simple_system m (rvars_monom hm) k2.n k2.r k2.rj indices
      end 
    | [h1; h2] ->
      begin match h1.hv_gname, h2.hv_gname with
      | G1, G1 -> double_system m (rvars_monom hm) k1.n k1.r k1.rj k1.n k1.r k1.rj indices
      | G2, G2 -> double_system m (rvars_monom hm) k2.n k2.r k2.rj k2.n k2.r k2.rj indices
      | G1, G2 
      | G2, G1 -> double_system m (rvars_monom hm) k1.n k1.r k1.rj k2.n k2.r k2.rj indices
      end
    | _::_::_::_ | [] ->
      failwith "Not supported"
  in
  smt_solver system

let stable (eq : constr) (s : sum) k1 k2 =
  if (eq.qvars = [] && eq.is_eq = Eq) then (
    let handle_mons = L.filter (mons eq.poly) ~f:(fun m -> rvars m <> []) in
    if (L.exists handle_mons ~f:(fun hm -> overlap s.monom hm k1 k2))
    then [eq]
    else
      let rvs = rvars s.monom in
      let poly1 =
        Map.filter eq.poly
       	  ~f:(fun ~key:s_eq ~data:_c ->
                not (equal_monlist (rvars s_eq.monom) rvs && hvars s_eq.monom = []))
      in
      let constr1 = { qvars = []; is_eq = Eq; poly = poly1 } in
      let constr2 = { qvars = s.ivars; is_eq = Eq; poly = coeff eq.poly s.monom} in
      [ constr1; constr2 ]
  ) else ( [eq] )

(* ----------------------------------------------------------------------- *)
(* Case distinctions *)

let remove_forall (c : constr) =
  {c with qvars = L.filter c.qvars ~f:(fun x -> L.mem (Ivar.Set.to_list (ivars_constr c)) x )}
    
let power_poly (p : poly) (e : BI.t) =
  let rec aux p' n = if BI.is_one n then p' else aux (mult_poly p' p) BI.(n -! one) in
  if BI.(compare e zero) < 0 then failwith "Not suported"
  else if BI.(compare e zero) = 0 then SP.one else aux p e 
						       
let subst_sum (c : BI.t) (s : sum) (par : atom) (value : poly) =
  let d = degree par s.monom in
  let s = {s with monom = Map.remove s.monom par} in
  Map.fold (power_poly value d) ~init:(mk_poly [])
	   ~f:(fun ~key:s' ~data:c' p -> add_poly p (mk_poly [(BI.(c *! c'), mult_sum s s')]))
	   
(* not use this function with bound parameters *)
let subst (c : constr_conj) (par : atom) (value : poly) =
  List.map c ~f:(fun x -> {x with poly = Map.fold x.poly ~init:(mk_poly [])
		~f:(fun ~key:s ~data:c p -> add_poly p (subst_sum c s par value) )}  )

let subst_bound_sum c s qvars = function
  | Param (name, Some _) ->
     let filt = Map.filter s.monom
	 ~f:(fun ~key:k ~data:_v -> match k with
				  | Param (name', Some i) when name' = name && L.mem (s.ivars @ qvars) i -> true
				  | _ -> false) in
     if Map.is_empty filt then mk_poly [(c,s)]
     else mk_poly []
  | _ -> failwith "Indexed parameter expected"
	   
let subst_bound_by_zero (c : constr_conj) (par : atom) =
  List.map c ~f:(fun x -> {x with poly = Map.fold x.poly ~init:(mk_poly [])
	     ~f:(fun ~key:s ~data:c p -> add_poly p (subst_bound_sum c s x.qvars par) )}  )
  |> List.map ~f:remove_forall

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
  if sum.ivars<>[] then 
    F.fprintf fmt "@[<hov 2>(%a%a)@]"
      (pp_binder "sum") sum.ivars
      pp_monom sum.monom
  else
    F.fprintf fmt "@[<hov 2>%a@]"
      pp_monom sum.monom

let pp_term fmt (s,c) =
  if BI.is_one c
  then pp_sum fmt s
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

let pp_constr fmt { qvars = qvs; poly = p; is_eq = is_eq } =
  F.fprintf fmt "@[<hv 2>%a%a %s 0@]" (pp_binder "forall") qvs pp_poly p (is_eq_to_string is_eq)

let pp_constr_conj fmt conj =
  let rec aux n list f =
    match list with
    | [] -> F.fprintf f "\n"
    | c :: rest ->
       F.fprintf f "@[%i: %a@]@\n" n pp_constr c;
       F.fprintf f "%t" (aux (n+1) rest)
  in
  aux 1 conj fmt
    
