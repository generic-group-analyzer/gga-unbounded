open Core_kernel.Std
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
let equal_sum a b = Set.equal (Ivar.Set.of_list a.ivars) (Ivar.Set.of_list b.ivars) &&
		    Set.equal (Ivar_Pair.Set.of_list a.i_ineq) (Ivar_Pair.Set.of_list b.i_ineq) &&
		    equal_monom a.monom b.monom
let equal_poly a b = compare_poly a b = 0
let equal_constr a b = Set.equal (Ivar.Set.of_list a.qvars) (Ivar.Set.of_list b.qvars) &&
		       Set.equal (Ivar_Pair.Set.of_list a.q_ineq) (Ivar_Pair.Set.of_list b.q_ineq) &&
		       equal_is_eq a.is_eq b.is_eq &&
		       equal_poly a.poly b.poly
let equal_constr_conj a b = compare_constr_conj a b = 0
let equal_constr_disj a b = compare_constr_disj a b = 0

(* ----------------------------------------------------------------------- *)
(* variable occurences *)

let ivars_pairs pairs =
  L.fold_left pairs
   ~init:Ivar.Set.empty
   ~f:(fun s (i,j) -> Set.union s (Ivar.Set.of_list [i;j]))

let ivars_monom mon =
  Map.fold mon
    ~init:Ivar.Set.empty
    ~f:(fun ~key:k ~data:_v se -> Set.union se (ivars_atom k))

let ivars_sum sum =
  Set.union (ivars_monom sum.monom) (Ivar.Set.of_list sum.ivars)
  (*|> Set.union (ivars_pairs sum.i_ineq)*)

let ivars_poly poly =
  L.fold_left (Map.keys poly)
    ~init:Ivar.Set.empty
    ~f:(fun se1 t -> Set.union se1 (ivars_sum t)
           |> Set.union (ivars_pairs t.i_ineq))

let ivars_constr constr =
  Set.union (ivars_poly constr.poly) (Ivar.Set.of_list constr.qvars)

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
  go old_idx.id

let renaming_away_from taken ivars =
  Set.fold ivars ~init:(Ivar.Map.empty,taken)
    ~f:(fun (m,taken) ivar ->
          let ivar' = new_ivar taken ivar in
          (Map.add m ~key:ivar ~data:ivar', Set.add taken ivar'))

let apply_renaming rn ivar =
  Option.value ~default:ivar (Map.find rn ivar)

let free_ivars_sum s =
  (Set.diff (ivars_sum s) (Ivar.Set.of_list s.ivars))

let free_ivars_poly p =
  Map.fold p
    ~init:Ivar.Set.empty
    ~f:(fun ~key:s ~data:_c se -> Set.union se (free_ivars_sum s))

let free_ivars_constr c =
  Set.diff (free_ivars_poly c.poly) (Ivar.Set.of_list c.qvars)

let free_ivars_constr_conj constraints =
  L.fold_left constraints
   ~init:Ivar.Set.empty
   ~f:(fun s c -> Set.union s (free_ivars_constr c))

let bound_ivars_poly p =
  Map.fold p
    ~init:Ivar.Set.empty
    ~f:(fun ~key:s ~data:_c se -> Set.union se (Ivar.Set.of_list s.ivars))

let bound_ivars_constr_conj constraints =
  L.fold_left constraints
   ~init:Ivar.Set.empty
   ~f:(fun se c -> Set.union se (bound_ivars_poly c.poly)
		   |> Set.union (Ivar.Set.of_list c.qvars)
      )

let all_pairs (ivars : ivar list) =
  L.filter (L.cartesian_product ivars ivars) ~f:(fun (x,y) -> x <> y)
  |> L.dedup ~compare:Ivar_Pair.compare

let all_ivar_distinct membership update_t rename ivars_t t =
  let rec do_split x = function
    | [] -> [x]
    | (i,j) :: rest_pairs ->
       if membership x (i,j) then do_split x rest_pairs
       else
	 let ts1 = do_split (update_t x (i,j)) rest_pairs in
	 let ts2 = do_split (rename x i j) (all_pairs (ivars_t (rename x i j))) in
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

(* Converts sum(i,j; a_i) into Q*sum(i; a_i) *)
let sum2Q unused ivs ivs_pairs =
  let exceptions =
    L.fold_left ivs_pairs
     ~init:[]
     ~f:(fun l (x,y) -> if equal_ivar unused x then y :: l
			else if equal_ivar unused y then x :: l
			else l)
  in
  let bound_exceptions = L.filter exceptions ~f:(fun x -> L.mem ivs x ~equal:equal_ivar) in
  let free_exceptions = L.filter exceptions ~f:(fun x -> not (L.mem ivs x ~equal:equal_ivar)) in
  let b = L.fold_left bound_exceptions
           ~init:true
	   ~f:(fun b i ->
	       let exceptions_i =
		 L.fold_left ivs_pairs
                  ~init:[]
		  ~f:(fun l (x,y) -> if equal_ivar i x then y :: l
				     else if equal_ivar i y then x :: l
				     else l)
	       in
	       b && (L.fold_left free_exceptions
                      ~init:true
		      ~f:(fun b' j -> b' && (L.mem exceptions_i j ~equal:equal_ivar))
		    )
	      )
  in
  b, BI.of_int (- (L.length exceptions))

let mk_sum ivs ivs_dist mon =
  (*let ivs_monom = Set.to_list (ivars_monom mon) in*)
  (*let ivs_dist = L.filter ivs_dist ~f:(fun (x,y) -> L.mem (ivs@ivs_monom) x || L.mem (ivs@ivs_monom) y) in*)
  (*let ivs_dist = L.filter ivs_dist ~f:(fun (x,y) -> L.mem ivs x ~equal:equal_ivar || L.mem ivs y ~equal:equal_ivar) in *)
  let ivar_pairs = Ivar_Pair.Set.to_list (Ivar_Pair.Set.of_list ivs_dist) in
  let unused_ivars = Set.diff (Ivar.Set.of_list ivs) (ivars_monom mon) in
  let again_ivs, qpart =
    L.fold_left (Ivar.Set.to_list unused_ivars)
     ~init:([],[])
     ~f:(fun (idxs,qlist) i ->
	 let b, n = sum2Q i ivs ivar_pairs in
	 if b then (idxs, Nqueries(n) :: qlist)
	 else (i :: idxs, qlist)
	)
  in
  let ivs = (Ivar.Set.to_list (Set.diff (Ivar.Set.of_list ivs) unused_ivars)) @ again_ivs in
  let new_mon = L.fold_left (list2multiplicity qpart ~equal:Atom.equal)
                 ~init:mon
                 ~f:(fun m (q,n) -> Map.add m ~key:q ~data:(BI.of_int n))
  in
  { ivars = ivs; i_ineq = ivar_pairs; monom = new_mon }

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
  let membership s (i,j) = Set.mem (Ivar_Pair.Set.of_list s.i_ineq) (i,j) in
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
  let ivs = L.dedup ~compare:compare_ivar ivs in
  let ivs = L.filter ivs ~f:(fun i -> Set.mem (ivars_poly poly) i) in
  let ivar_pairs = L.dedup ~compare:Ivar_Pair.compare ivs_dist in
  (* let ivar_pairs = L.filter ivar_pairs ~f:(fun (x,y) -> L.mem ivs x || L.mem ivs y) in *)
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
          (mk_poly [(c, mk_sum (L.map ~f s.ivars)
			       (L.map ~f:(fun(x,y) -> (f x, f y)) s.i_ineq)
			       (map_idx_monom ~f s.monom))]))

let all_ivar_distinct_constr_conj conj =
  let membership c (i,j) = L.mem c.q_ineq (i,j) in
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
  let opp a = opp_poly a
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
    F.fprintf fmt "@[<hov 2>%a@]"
	      (pp_list " * " pp_atom_pow) (Map.to_alist mon)
  else
    F.fprintf fmt "@[<hov 2>1@]"

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
  else if sum.i_ineq <> [] then
      F.fprintf fmt "@[<hov 2>(%a)%a@]"
      (pp_list ", " pp_ivar_pair) sum.i_ineq
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
       F.fprintf f "@[%i: %a@]@\n\n" n pp_constr c;
       F.fprintf f "%t" (aux (n+1) rest)
  in
  aux 1 conj fmt

(*
let pp_int fmt i =
  F.fprintf fmt "%i" i
*)

(* ----------------------------------------------------------------------- *)
(* isomorphic constraints *)

let rename_sum s rn =
  let ivars = L.map s.ivars ~f:(apply_renaming rn) in
  let i_ineq = L.map s.i_ineq ~f:(fun (x,y) -> (apply_renaming rn x, apply_renaming rn y)) in
  let monom = map_idx_monom ~f:(apply_renaming rn) s.monom in
  mk_sum ivars i_ineq monom

let rename_poly p rn =
  Map.fold p
     ~init:SP.zero
     ~f:(fun ~key:s ~data:c p' -> SP.(p' +! (mk_poly [(c,rename_sum s rn)]) ) )

let rename_constr c rn =
  let qvars = L.map c.qvars ~f:(apply_renaming rn) in
  let q_ineq = L.map c.q_ineq ~f:(fun (x,y) -> (apply_renaming rn x, apply_renaming rn y)) in
  let poly = rename_poly c.poly rn in
  mk_constr qvars q_ineq c.is_eq poly

let matching_term (c1,s1) (c2,s2) ren =
  let free1 = L.filter (Set.to_list (free_ivars_sum s1)) ~f:(fun x -> (Ivar.Map.find ren x)=None) in
  let free2 = L.filter (Set.to_list (free_ivars_sum s2)) ~f:(fun x -> (Ivar.Map.find ren x)=None) in
  let bound1 = s1.ivars in
  let bound2 = s2.ivars in
  if (BI.compare c1 c2 <> 0) ||
     (L.length free1 <> L.length free2) || (L.length bound1 <> L.length bound2) then []
  else
    let f_perms = perms free1 in
    let b_perms = perms bound1 in

    let rec aux output f_list b_list =
    match f_list with
      | [] -> output
      | f::rest_f ->
	 begin match b_list with
	 | [] -> aux output rest_f b_perms
	 | b::rest_b ->
	    let rn = Ivar.Map.of_alist_exn (L.zip_exn (f @ b) (free2 @ bound2)) in
	    if equal_sum (rename_sum s1 rn) s2 then
	      let new_rn = Ivar.Map.of_alist_exn ((Map.to_alist ren) @ (L.zip_exn f free2)) in
	      aux (new_rn :: output) rest_f rest_b
	    else
	      aux output f_list rest_b
	 end
    in
    aux [] f_perms b_perms

let invert_rn rn =
  let (k,v) = L.unzip (Map.to_alist rn) in
  Ivar.Map.of_alist_exn (L.zip_exn v k)

let matching_poly p1 p2 =
  let rec aux xs ys ren =
    match xs with
    | [] -> [ren]
    | (s1,c1)::rest_xs ->
       let renamings = L.map ys ~f:(fun (s2,c2) -> matching_term (c1,s1) (c2,s2) ren) in
       let ys_residues = rm_diagonal ys in
       let rename_terms terms rn = L.map terms ~f:(fun (s,c) -> (rename_sum s (invert_rn rn), c)) in
       let residues = L.map2_exn renamings ys_residues
		      ~f:(fun rns terms -> L.map rns ~f:(rename_terms terms)) in
       L.map2_exn (L.concat renamings) (L.concat residues)
	~f:(fun rn ys_rest -> aux rest_xs ys_rest rn)
       |> L.concat
  in
  if (Map.length p1) <> (Map.length p2) then []
  else aux (Map.to_alist p1) (Map.to_alist p2) (Ivar.Map.empty)

let matching_constr c1 c2 = (* This does not check the q_ineq *)
  let valid_rn rn =
    let (ivars1, ivars2) = L.unzip (Map.to_alist rn) in
    L.map2_exn ivars1 ivars2
     ~f:(fun i j -> ((L.mem ~equal:equal_ivar c1.qvars i) && (L.mem ~equal:equal_ivar c2.qvars j)) ||
	  (not ((L.mem ~equal:equal_ivar c1.qvars i) || (L.mem ~equal:equal_ivar c2.qvars j))) && (equal_ivar i j)  )
    |> L.fold_left ~init:true ~f:(&&)
  in
  L.filter (matching_poly c1.poly c2.poly) ~f:(valid_rn)

let isomorphic_sum s1 s2 = L.length (matching_term (BI.one,s1) (BI.one,s2) Ivar.Map.empty) > 0
let isomorphic_constr c1 c2 =
(*let () = F.printf "%a [%a] [%a] ?=? %a [%a] [%a] -> %b %b\n" pp_constr c1 (pp_list "," pp_ivar) c1.qvars (pp_list "," pp_ivar_pair) c1.q_ineq pp_constr c2 (pp_list "," pp_ivar) c2.qvars (pp_list "," pp_ivar_pair) c2.q_ineq (equal_is_eq c1.is_eq c2.is_eq) ((L.length (matching_constr c1 c2) > 0 ||
   L.length (matching_constr c1 { c2 with poly = SP.opp c2.poly }) > 0)) in
  F.print_flush();*)
 equal_is_eq c1.is_eq c2.is_eq &&
  (L.length (matching_constr c1 c2) > 0 ||
   L.length (matching_constr c1 { c2 with poly = SP.opp c2.poly }) > 0)
let isomorphic_poly p1 p2 = L.length (matching_constr (mk_constr [] [] Eq p1) (mk_constr [] [] Eq p2)) > 0
