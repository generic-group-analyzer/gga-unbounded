open Core_kernel.Std
open Util
open Abbrevs
open Watom
open Wconstrs
open Sage
open Z3

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

let bound_by_sum (s : sum) = function
  | Rvar (_, None) -> false
  | Rvar (_, Some i) -> L.mem ~equal:equal_ivar s.ivars i
  | Param (_, None) -> false
  | Param (_, Some i) -> L.mem ~equal:equal_ivar s.ivars i
  | _ -> failwith "bound_by_sum: expected parameter as second argument"
						   
let not_bound_sum_params s =
  let (parameters, _) = L.unzip (params s.monom) in
  L.filter ~f:(fun p -> not (bound_by_sum s p)) parameters

let not_bound_sum_vars s =
  let (variables, _) = L.unzip (rvars s.monom) in
  L.filter ~f:(fun v -> not (bound_by_sum s v)) variables	   
						   
let coeff_term c s mon =
  if (equal_monlist (rvars s.monom) (rvars mon)) &&
     (equal_monlist (hvars s.monom) (hvars mon))
  then mk_poly [(c, mk_sum s.ivars s.i_ineq (params_monom s.monom))]
  else mk_poly []
	 
let nchoosek_perm list k =
    let rec aux output list k =
    if k = 0 then output
    else
      aux (L.concat ( L.map output ~f:(fun l -> L.map list ~f:(fun x -> x::l) ) )) list (k-1)
  in
  aux [[]] list k
  |> L.filter ~f:(fun l -> L.length (L.dedup ~compare:compare_ivar l) = L.length l)
      
let coeff_sum (c : BI.t) (s : sum) (idxs, mon) =
  if (L.length s.ivars < L.length idxs) then mk_poly []
  else
    let (rn,_) = renaming_away_from (Ivar.Set.of_list idxs) (Ivar.Set.of_list s.ivars) in
    let s = rename_sum s rn in
    let idx_perms = nchoosek_perm s.ivars (L.length idxs) in
    let renamings = L.map idx_perms ~f:(fun l -> Ivar.Map.of_alist_exn (L.zip_exn l idxs)) in
    let monomials = L.map renamings ~f:(fun rn -> map_idx_monom ~f:(apply_renaming rn) s.monom) in
    let new_ivars = L.map idx_perms ~f:(fun l -> L.filter s.ivars
						 ~f:(fun i -> not (L.mem ~equal:equal_ivar l i))) in
    L.map2_exn monomials new_ivars ~f:(fun m ivs -> coeff_term c (mk_sum ivs s.i_ineq m) mon)
    |> L.fold_left ~init:(mk_poly []) ~f:SP.(+!)
      
let coeff (p : poly) (idxs, mon) =
  Map.fold p
    ~init:(mk_poly [])
	  ~f:(fun ~key:s ~data:c p -> SP.(p +! (coeff_sum c s (idxs, mon)) ))

let mons (p : poly) =
  Map.fold p
    ~init:[]
	  ~f:(fun ~key:s ~data:_c list ->
          (Map.filter s.monom ~f:(fun ~key:v ~data:_e -> not (is_param v))) :: list)

let mons_hvar_free (p : poly) =
  Map.fold p
    ~init:[]
	  ~f:(fun ~key:s ~data:_c list ->
          (Map.filter s.monom ~f:(fun ~key:v ~data:_e -> not (is_param v) && not(is_hvar v))) :: list)

let degree (v : atom) (m : monom) =
  Option.value ~default:BI.zero (Map.find m v)

(* ----------------------------------------------------------------------- *)
(* Adversary knowledge data type *)

type k_inf = {
  non_recur : monom list  ; (* non-recursive knowledge in G_i *)
  recur     : monom list  ; (* recursive knowledge in G_i *)
  recur_idx : monom list  ; (* recursive indexed knowledge in G_i *)
}

(* ----------------------------------------------------------------------- *)
(* Substitute free occurence of index variable *)

let subst_idx_pairs (i : ivar) (j : ivar) pairs =
  let f x = if x = i then j else x in
  L.map pairs ~f:(fun (i1,i2) -> (f i1, f i2))
	       
let subst_idx_sum (i : ivar) (j : ivar) (s : sum) =
  if L.mem s.ivars i
  then failwith "subst_idx_sum: cannot substitute Sum-bound index variable bound"
  else mk_sum s.ivars (subst_idx_pairs i j s.i_ineq) (map_idx_monom ~f:(fun x -> if x = i then j else x) s.monom)
	   
let subst_idx_poly (i : ivar) (j : ivar) (p : poly) =
  Map.fold p
    ~init:(mk_poly [])
	  ~f:(fun ~key:s ~data:c p -> SP.(p +! (mk_poly [(c, subst_idx_sum i j s)])))
	   	   
let subst_idx_constr (i : ivar) (j : ivar) (c : constr) =
  if L.mem c.qvars i then failwith "subst_idx_sum: impossible to substitute a bound variable"
  else mk_constr c.qvars (subst_idx_pairs i j c.q_ineq) c.is_eq (subst_idx_poly i j c.poly)
		 
let rm_from_pairs (i : ivar) (pairs : ivar_pair list) =  
  L.filter pairs ~f:(fun (x,y) -> x <> i && y <> i)

let keep_from_pairs (i : ivar) (pairs : ivar_pair list) =
  L.filter pairs ~f:(fun (x,y) -> x = i || y = i)
	   
(* ----------------------------------------------------------------------- *)
(* Split forall and sum quantification as follows:
   split(i', forall i. e) = split(i',e)[i -> i'] /\ (forall i\{i'}. (split(i',e)))
   split(i', sum i. e) = split(i',e)[i -> i'] + (sum i\{i'}. (split(i',e)))
*)

let not_iineq_contradiction (s : sum) =
  let f (i,j) = equal_ivar i j in
  not (L.exists ~f s.i_ineq)

let not_qineq_contradiction (c : constr) =
  let f (i,j) = equal_ivar i j in
  not (L.exists ~f c.q_ineq)
	   
let split_sum (iv : ivar) (sum : sum) =
  let rec do_split s =
    match s.ivars with      
    | [] -> [s]
    | i::is -> 
       let sums = do_split (mk_sum is s.i_ineq s.monom) in
       let sums1 = L.map ~f:(fun s' -> mk_sum (i::s'.ivars) ((i,iv)::(s'.i_ineq@s.i_ineq)) s'.monom) sums in
       let sums2 = L.map ~f:(subst_idx_sum i iv) sums in
       if (L.mem s.i_ineq ~equal:Ivar_Pair.equal (i,iv)) then sums1
       else
	 L.filter ~f:not_iineq_contradiction (sums1 @ sums2)
  in  
  if L.mem sum.ivars iv
  then failwith "split_sum: given index variable must be fresh"
  else do_split sum
         
let split_poly (iv : ivar) (p : poly) =
  Map.fold p ~init:SP.zero
	     ~f:(fun ~key:s ~data:c p1 ->
             let p2 = mk_poly (L.map ~f:(fun s -> (c,s)) (split_sum iv s)) in
	           SP.(p1 +! p2))
      
let split_constr (iv : ivar) (constr : constr) =
  let rec do_split c =
    match c.qvars with
    | [] -> [ mk_constr [] c.q_ineq c.is_eq (split_poly iv c.poly) ]
    | i::is -> 
       let constrs = do_split (mk_constr is c.q_ineq c.is_eq c.poly) in
       let constrs1 = L.map ~f:(fun x -> mk_constr (i::x.qvars) ((i,iv)::(x.q_ineq@c.q_ineq)) x.is_eq x.poly) constrs in
       let constrs2 = L.map ~f:(subst_idx_constr i iv) constrs in
       if (L.mem c.q_ineq ~equal:Ivar_Pair.equal (i,iv)) then constrs1
       else
	 L.filter ~f:not_qineq_contradiction (constrs1 @ constrs2)
  in
  if L.mem constr.qvars iv
  then failwith (fsprintf "split_constr: given index variable %a not fresh" pp_ivar iv)
  else do_split constr
       
let split (iv : ivar) (conj : constr_conj) =
  List.concat_map conj ~f:(split_constr iv)
      
(* ----------------------------------------------------------------------- *)
(* Case distinctions *)

let power_poly (p : poly) (e : BI.t) =
  let rec aux p' n = if BI.is_one n then p' else aux SP.(p' *! p) BI.(n -! one) in
  if BI.(compare e zero) < 0 then failwith "Not supported"
  else if BI.(compare e zero) = 0 then SP.one else aux p e 
						       
let subst_sum (c : BI.t) (s : sum) (par : atom) qvars (value : poly) =
  let d = degree par s.monom in
  let s = mk_sum s.ivars s.i_ineq (Map.remove s.monom par) in
  let (rn,_) = renaming_away_from (Ivar.Set.of_list qvars) (bound_ivars_poly value) in
  let new_value = rename_poly value rn in
  Map.fold (power_poly new_value d) ~init:(mk_poly [])
	   ~f:(fun ~key:s' ~data:c' p -> SP.(p +! (mk_poly [(BI.(c *! c'), mult_sum s s')])))
	   
(* not use this function with bound parameters *)
let subst (c : constr_conj) (par : atom) (value : poly) =
  let subst_poly p qvars =
    Map.fold p ~init:(mk_poly [])
		  ~f:(fun ~key:s ~data:c p -> SP.(p +! (subst_sum c s par qvars value)))
  in
  List.map c ~f:(fun x -> mk_constr x.qvars x.q_ineq x.is_eq (subst_poly x.poly x.qvars))

let subst_bound_sum c s qvars value exceptions q_excpt = function
  | Param (name, Some par_idx) ->
     let filt =
       Map.filter s.monom ~f:(fun ~key:k ~data:_v ->
	   match k with
	   | Param (name', Some i) ->
	      let excpt = L.map exceptions ~f:(fun k -> (i,k)) in
	      String.equal name' name && 
		((L.mem s.ivars i ~equal:equal_ivar && sub_list excpt s.i_ineq ~equal:equal_ivar_pair) ||
		 (L.mem qvars i ~equal:equal_ivar && sub_list excpt q_excpt ~equal:equal_ivar_pair))
	   | _ -> false) in
     if Map.is_empty filt then mk_poly [(c,s)]
     else
       let residue = Map.filter s.monom ~f:(fun ~key:k ~data:_v ->
		      match k with
		      | Param (name', Some i) ->
			 let excpt = L.map exceptions ~f:(fun k -> (i,k)) in
			 let b = String.equal name' name && 
			   ((L.mem s.ivars i ~equal:equal_ivar && sub_list excpt s.i_ineq ~equal:equal_ivar_pair) ||
			    (L.mem qvars i ~equal:equal_ivar && sub_list excpt q_excpt ~equal:equal_ivar_pair))
			 in
			 not b
		      | _ -> true)
       in
       let poly_inside_sum = 
	 Map.fold filt
	    ~init:( mk_poly [(c, mk_sum [] [] residue)] )
	    ~f:(fun ~key:k ~data:v p ->
		let k_ivar = L.hd_exn (Set.to_list (ivars_atom k)) in
		let new_value = rename_poly value (Ivar.Map.of_alist_exn [(par_idx, k_ivar)]) in
		let (rn,_) = renaming_away_from (Ivar.Set.of_list qvars) (bound_ivars_poly new_value) in
		let new_value = rename_poly new_value rn in
		SP.( p *! (power_poly new_value v))		  
	       )
       in
       Map.fold poly_inside_sum
          ~init:SP.zero
	  ~f:(fun ~key:s' ~data:c' p ->
	      SP.( p +! (mk_poly [(c', mk_sum (s.ivars @ s'.ivars) (s.i_ineq @ s'.i_ineq) s'.monom )])))

  | _ -> failwith "Indexed parameter expected"
	   
let subst_bound (c : constr_conj) (par : atom) (exceptions : ivar list) (value : poly) =
  let subst_poly p qvars q_excpt =
    Map.fold p ~init:(mk_poly [])
	     ~f:(fun ~key:s ~data:c p -> SP.(p +! (subst_bound_sum c s qvars value exceptions q_excpt par)))
  in
  List.map c
	   ~f:(fun x -> mk_constr x.qvars x.q_ineq x.is_eq (subst_poly x.poly x.qvars x.q_ineq))

let fresh_ivar (c : constr_conj) =
  let taken_ivars = ivars_conj c in
  new_ivar taken_ivars (Option.value ~default:{name = "i"; id = 0} (Set.choose taken_ivars))

let free_idx constraints i =
  L.fold_left constraints
   ~init:false
   ~f:(fun free c -> free || (Ivar.Set.mem (free_ivars_constr c) i))	      
	   
let case_dist (c : constr_conj) par =
  match par with
  | Param (_, None) ->
     let c1 = subst c par SP.zero in
     let c2 = (mk_constr [] [] InEq (SP.of_a par)) :: c in
     [ c1; c2 ]
  | Param (name, Some i) ->
     if (free_idx c i) then
       let c1 = subst c par SP.zero in
       let c2 = (mk_constr [] [] InEq (SP.of_a par)) :: c in
       [ c1; c2 ]
     else
       let c1 = subst_bound c par [] SP.zero in
       let i = fresh_ivar c in
       let c2 = (mk_constr [] [] InEq (SP.of_a (mk_param ~idx:(Some i) name))) :: (split i c) in
       [ c1; c2 ]			   
  | _ -> failwith "case_dist: second argument has to be a parameter"

(* ----------------------------------------------------------------------- *)
(* Uniform indices *)

let nice_renaming_ivars (s : sum) iname taken =
  let new_ivars = L.map (range 1 (L.length s.ivars))
                   ~f:(fun n -> { name = Char.to_string (Char.of_int_exn (iname+n-1)) ; id = 0 }) in
  let (rn_ivars, _) = renaming_away_from taken (Ivar.Set.of_list new_ivars) in
  let rn = Ivar.Map.of_alist_exn (L.zip_exn s.ivars (Map.data rn_ivars)) in
  rename_sum s rn
	      
let uniform_bound_poly (p : poly) (letter : int) =
  let free = free_ivars_poly p in
  Map.fold p
     ~init:SP.zero
     ~f:(fun ~key:s ~data:c p' ->
	 SP.(p' +! (mk_poly [(c, nice_renaming_ivars s letter free)])) )

let nice_renaming_qvars (c : constr) iname taken =
  let new_qvars = L.map (range 1 (L.length c.qvars)) 
                   ~f:(fun n -> { name = Char.to_string (Char.of_int_exn (iname+n-1)) ; id = 0 }) in
  let (rn_qvars, _) = renaming_away_from taken (Ivar.Set.of_list new_qvars) in
  let rn = Ivar.Map.of_alist_exn (L.zip_exn c.qvars (Map.data rn_qvars)) in
  rename_constr c rn

let uniform_qvars_constraints (constraints : constr_conj) =
  let free = free_ivars_constr_conj constraints in
  let sum_bound = L.fold_left constraints
                   ~init:Ivar.Set.empty
		   ~f:(fun s c -> Set.union s (bound_ivars_poly c.poly))
  in
  L.map constraints
   ~f:(fun c -> nice_renaming_qvars c 105 (Set.union free sum_bound))		   

let clear_non_used_idxs constraints =
  let clear_poly p ivs =
    Map.fold p
       ~init:SP.zero
       ~f:(fun ~key:s ~data:c p' -> 
	 SP.(p' +! (mk_poly [(c, mk_sum s.ivars (L.filter s.i_ineq 
                                                  ~f:(fun (x,y) -> L.mem (s.ivars @ ivs) x && L.mem (s.ivars @ ivs) y)) s.monom)]))
          
)
  in
  let free = Set.to_list (free_ivars_constr_conj constraints) in
  L.map constraints
   ~f:(fun c -> 
       let ivs = c.qvars @ free in
       let new_q_ineq = L.filter c.q_ineq ~f:(fun (x,y) -> L.mem ivs x && L.mem ivs y) in
       mk_constr c.qvars new_q_ineq c.is_eq (clear_poly c.poly (c.qvars @ free))
      )

let uniform_bound constraints =
  let constraints = clear_non_used_idxs constraints in
  let free = Set.to_list (free_ivars_constr_conj constraints) in
  let bound = Set.to_list (bound_ivars_constr_conj constraints) in
  let rn = Ivar.Map.of_alist_exn 
	     (L.zip_exn (free @ bound)
	        ((L.map free ~f:(fun i -> {i with name = "free"^i.name})) @
		(L.map bound ~f:(fun i -> {i with name = "bound"^i.name})) )
	     )
  in
  let n_qvars = L.fold_left constraints
                 ~init:0
                 ~f:(fun m c -> if (L.length c.qvars) > m then L.length c.qvars else m)
  in
  let new_constraints =
    L.map constraints 
     ~f:(fun c -> 
	 let c = rename_constr c rn in
	 let p = L.fold_left c.qvars
		  ~init:(uniform_bound_poly c.poly (n_qvars+105))
		  ~f:(fun p i -> split_poly i p)
	 in       
	 mk_constr c.qvars c.q_ineq c.is_eq p)
    |> uniform_qvars_constraints

  in
  (* No variable has id > 1 at this point *)
  let free2 = free_ivars_constr_conj new_constraints in
  let rn2 = Ivar.Map.of_alist_exn
	      (L.zip_exn (Set.to_list free2)
			 (L.map (range 1 (Set.length free2)) ~f:(fun n -> {name = "i"; id = n}))
	      )
  in
  L.map new_constraints ~f:(fun c -> rename_constr c rn2)
  |> clear_non_used_idxs

(* ----------------------------------------------------------------------- *)
(* Simplify by zero *)
	
let remove_constants (p : poly) =
  let coefficients = (Map.fold p ~init:[] ~f:(fun ~key:_s ~data:c l -> c :: l)) in
  let gcd = BI.abs (gcd_big_int_list coefficients) in
  let freq_sign = most_frequent_sign coefficients in
  group_order_bound := BI.(max !group_order_bound (one +! gcd ));
  Map.fold p ~init:SP.zero ~f:(fun ~key:s ~data:c p' -> SP.(p' +! (mk_poly [(BI.(c /! gcd *! freq_sign),s)])) )
  (* Be carefull, the group order has to be distinct from gcd!!! *)
   
let clear_equations (constraints : constr_conj) =
  let f c = (equal_poly c.poly SP.zero && c.is_eq = Eq) ||
	    (equal_poly c.poly SP.one  && c.is_eq = InEq)
  in
  L.map constraints ~f:(fun c -> mk_constr c.qvars c.q_ineq c.is_eq (remove_constants c.poly))
  |> L.filter ~f:(fun c -> not (f c))

let known_not_null (p : poly) (constraints : constr_conj) =
  if (equal_poly p SP.zero) then false
  else
    let p = remove_constants p in
    let not_null = L.map (L.filter (clear_equations constraints) ~f:(fun c -> c.is_eq = InEq))
		    ~f:(fun c -> c.poly) in
    (L.mem ~equal:isomorphic_poly (SP.one :: not_null) p)
	     
let collect_pairs list =
  let rec aux output = function
    | [] -> output
    | (p,d) :: rest ->
       let p'' = L.fold_left rest
		    ~init:p
		    ~f:(fun p'' (p',d') -> if (BI.equal d d') then SP.(p'' +! p') else p'') in
       let rest = L.filter rest ~f:(fun (_,d') -> not (BI.equal d d')) in
       aux ((p'',d) :: output) rest
  in
  aux [] list
	
let sum2pair (c : BI.t) (s : sum) (a : atom) =
  if (bound_by_sum s a) then failwith "sum2pair: summation bound atom"
  else (mk_poly [(c, mk_sum s.ivars s.i_ineq (Map.remove s.monom a))],
	Option.value ~default:BI.zero (Map.find s.monom a))    
	      
let poly2pairs (p : poly) (a : atom) =
  Map.fold p ~init:[] ~f:(fun ~key:s ~data:c l -> (sum2pair c s a) :: l)
  |> collect_pairs

let pairs2poly pairs a =
  L.fold_left pairs
   ~init:SP.zero
   ~f:(fun p' (p,d) -> SP.(p' +! ((power_poly (of_a a) d)  *! p)) )	            

let f_pairs f pairs =
  let (_,degrees) = L.unzip pairs in
  match degrees with
  | [] -> BI.zero
  | d :: rest -> L.fold rest ~init:d ~f

let divide_by_par par c =
  let pairs = poly2pairs c.poly par in
  let minimum = f_pairs BI.min pairs in
  let new_poly = pairs2poly (L.map pairs ~f:(fun (p,d) -> (p, BI.(d -! minimum)) )) par in
  mk_constr c.qvars c.q_ineq c.is_eq new_poly

let remove_canceled_params constraints =
  let exceptions_from_pairs pairs i =
    L.fold_left pairs
     ~init:[]
     ~f:(fun l (i1,i2) -> if not(equal_ivar i i1) then i1 :: l else i2 :: l)
  in
  L.fold_left constraints
   ~init:constraints
   ~f:(fun constrs c ->
     match Map.keys c.poly with
     | sum :: [] when sum.ivars = [] && c.is_eq = Eq -> 
	begin match Map.keys sum.monom with
	| Param(_name, None) as param :: [] -> subst constrs param SP.zero
	| Param(_name, Some i) as param :: [] ->
	   if (L.mem c.qvars i ~equal:equal_ivar) then
	     subst_bound constrs param (exceptions_from_pairs c.q_ineq i) SP.zero  (* Consider idxs ineq !!! *)
	   else subst constrs param SP.zero
	| _ -> constrs
	end
     | sum :: [] when sum.ivars = [] && c.is_eq = InEq ->
	begin match Map.keys sum.monom with
	| Param(_,_) as param :: [] -> c :: (L.map constrs ~f:(divide_by_par param))
	| _ -> constrs
	end
     | _ -> constrs
   )
  

(* ----------------------------------------------------------------------- *)
(* Groebner Basis *)

let extract_not_bound_from_sum s =
  let new_monom, vars, degrees =
  Map.fold s.monom
     ~init:(Atom.Map.empty, [], [])
     ~f:(fun ~key:v ~data:d (new_monom, vars, degrees) ->
	 match v with
	 | Param (_, Some i) when L.mem s.ivars i ~equal:equal_ivar ->
	    (Map.add new_monom ~key:v ~data:d, vars, degrees)
	 | _ -> (new_monom, vars @ [v], degrees @ [d])
	)
  in
  (mk_sum s.ivars s.i_ineq new_monom), vars, degrees

let groebner_variables constraints =
  let gv_from_constr groebner_sums groebner_vars c =
    Map.fold c.poly
       ~init:(groebner_sums, groebner_vars)
       ~f:(fun ~key:s ~data:_c (gsums, gvars) ->
	   let (new_s, vars, _) = extract_not_bound_from_sum s in
	   if (L.length new_s.ivars > 0) && not(L.exists gsums ~f:(isomorphic_sum new_s)) then
	     (gsums @ [new_s]), (L.dedup ~compare:compare_atom (gvars @ vars))
	   else gsums, (L.dedup ~compare:compare_atom (gvars @ vars))
	  )
  in
  let rec aux groebner_sums groebner_vars = function
    | [] -> groebner_sums, groebner_vars
    | c :: rest -> 
       let new_sums, new_vars = gv_from_constr groebner_sums groebner_vars c in
       aux new_sums new_vars rest
  in
  (aux [] [] constraints), 
  L.fold_left constraints
   ~init:([],[])
   ~f:(fun (qvars,q_ineq) c -> (L.dedup (qvars @ c.qvars) ~compare:compare_ivar,
			        L.dedup (q_ineq @ c.q_ineq) ~compare:compare_ivar_pair)
      )

let constr2groebner_poly poly sums vars =
  let rec aux coefficients vars var_degree_map =
    match vars with
      | [] -> coefficients
      | v :: rest ->
	 aux (coefficients @ [match (Map.find var_degree_map v) with
			      | None -> BI.zero
			      | Some d -> d
			     ]
	     ) rest var_degree_map
  in
  let coefficients s =
    let (new_s, s_vars, degrees) = extract_not_bound_from_sum s in
    let sum_coefficients = 
      L.map sums ~f:(fun x -> if isomorphic_sum x new_s then BI.one else BI.zero)
    in
    sum_coefficients @ (aux [] vars (Atom.Map.of_alist_exn (L.zip_exn s_vars degrees)))
  in       
  Map.fold poly
     ~init:[]
     ~f:(fun ~key:s ~data:c gpoly -> gpoly @ [(c, coefficients s)] )

let permute_qvars constraints =
  let apply_perm p c =
    let aux_ivars = Ivar.Set.of_list (L.map c.qvars ~f:(fun i -> {i with name = "aux"^i.name})) in
    let (rn,_) = renaming_away_from (ivars_constr c) aux_ivars in
    let _, new_names = L.unzip (Map.to_alist rn) in
    let rn1 = Ivar.Map.of_alist_exn (L.zip_exn c.qvars new_names) in
    let rn2 = Ivar.Map.of_alist_exn (L.zip_exn new_names (first_n p (L.length c.qvars))) in
    rename_constr (rename_constr c rn1) rn2
  in
  let qvars = L.fold_left constraints
               ~init:Ivar.Set.empty
	       ~f:(fun se c -> Set.union se (Ivar.Set.of_list c.qvars))
  in
  let permutations = perms (Set.to_list qvars) in
  L.fold_left permutations
   ~init:[]
   ~f:(fun l p -> l @ (L.map constraints ~f:(fun c -> apply_perm p c)))

let groebner_polys constraints =
  (*let constraints = uniform_bound (all_ivar_distinct_constr_conj constraints) in*)
  (* We consider the equations in every combination of bound indices *)
  let constraints = L.filter ~f:(not_qineq_contradiction) (permute_qvars constraints) in
  let (sums, vars), (qvars, q_ineq) = groebner_variables constraints in
  let rec aux polynomials = function
    | [] -> polynomials
    | c :: rest -> aux (polynomials @ [constr2groebner_poly c.poly sums vars]) rest
  in
  aux [] constraints, sums, vars, qvars, q_ineq

let groebner_basis system =
  let () = () in
   (* F.printf "\n\n\n%s\n\n\n" ("{'cmd':'GroebnerBasis', 'equations':" ^ system ^ ", 'polynomials':[[[]]]}\n");
    F.printf "\n%s\n" (call_Sage ("{'cmd':'GroebnerBasis', 'equations':" ^ system ^ ", 'polynomials':[[[]]]}\n"));
    F.print_flush();*)
  call_Sage ("{'cmd':'GroebnerBasis', 'equations':" ^ system ^ ", 'polynomials':'[[[]]]'}\n")
  |> String.filter ~f:(fun c -> c <> '\n')
  |> String.filter ~f:(fun c -> c <> ' ')
  |> String.filter ~f:(fun c -> c <> '"')

let gbpolys2string polys =
  let rec singlepoly2string output = function
    | [] -> "[" ^ output ^ "]"
    | (c, coeffs) :: [] ->
       if (L.length coeffs > 0) then
	 let new_list = "[" ^ BI.to_string c ^ ", " ^
                        (String.concat ~sep:", " (L.map coeffs ~f:BI.to_string)) ^ "]" in
	 singlepoly2string (output ^ new_list) []
       else
	 singlepoly2string (output ^ "[" ^ BI.to_string c ^ ", 0]") []
    | (c, coeffs) :: rest ->
       if (L.length coeffs > 0) then
	 let new_list = "[" ^ BI.to_string c ^ ", " ^
		         (String.concat ~sep:", " (L.map coeffs ~f:BI.to_string)) ^ "]" in
	 singlepoly2string (output ^ new_list ^ ", ") rest
       else
	 singlepoly2string (output ^ "[" ^ BI.to_string c ^ ", 0], ") []
  in  
  let rec aux output = function
    | [] -> output
    | p :: [] -> output ^ (singlepoly2string "" p)
    | p :: rest -> aux (output ^ (singlepoly2string "" p) ^ ", ") rest
  in
  "'[" ^ (aux "" polys) ^ "]'"

let string2gbpoly string =
  let string2singlepoly p =
    let terms = String.split p ~on:'t' in
    L.map terms ~f:(fun t ->
		    let coeffs = String.split t ~on:',' in
		    let coeffs = L.map coeffs ~f:(Big_int.big_int_of_string) in
		    (L.hd_exn coeffs, L.tl_exn coeffs)
		   )
  in
  if string = "" then []
  else
    let polynomials = String.split string ~on:'p' in
    L.map polynomials ~f:(fun p -> string2singlepoly p)

let constraints_of_groebner_polys polys sums vars qvars q_ineq =
  let rec aux p exponents sums vars =
    match exponents, sums, vars with
    | [], _, _ -> p
    | exp :: rest_exps, [], v :: rest_vars ->
       aux SP.(p *! (power_poly (of_a v) exp)) rest_exps [] rest_vars
    | exp :: rest_exps, s :: rest_sums, _ ->
       aux SP.(p *! (power_poly (mk_poly [(BI.one, s)]) exp)) rest_exps rest_sums vars
    | _, [], [] -> p
  in
  L.map polys ~f:(fun p -> L.fold_left p
                            ~init:SP.zero
                            ~f:(fun p' (c,coeff) -> SP.(p' +! (of_const c) *! (aux SP.one coeff sums vars)) )
		 )
  |> L.map ~f:(fun p -> mk_constr qvars q_ineq Eq p)

(* Reduction *)
let simplify_poly_groebner_basis gb_equations polynomial ivars ivars_distinct = (* ivars are bound variables in the polynomial *)
  let bound = Set.to_list (bound_ivars_constr_conj gb_equations) in
  if (L.length ivars > L.length bound) then polynomial
  else
    let new_ivars = first_n bound (L.length ivars) in
    let rn = Ivar.Map.of_alist_exn (L.zip_exn ivars new_ivars) in
    let rn_poly = rename_poly polynomial rn in
    let constraint_of_poly = 
      mk_constr new_ivars (L.map ivars_distinct ~f:(fun (x,y) -> (apply_renaming rn x, apply_renaming rn y))) Eq rn_poly
    in

    let (sums, vars), (qvars, q_ineq) = groebner_variables (constraint_of_poly :: gb_equations) in
    let rec aux polynomials = function
      | [] -> polynomials
      | c :: rest -> aux (polynomials @ [constr2groebner_poly c.poly sums vars]) rest
    in
    let polys = aux [] (constraint_of_poly :: gb_equations) in
    (* sums should be empty *)
    let gb_system = gbpolys2string (L.tl_exn polys) in
    let poly_string = gbpolys2string [L.hd_exn polys] in
    (*F.printf "\n\n\n%s\n\n\n" ("{'cmd':'reduceModulo', 'equations':" ^ gb_system ^ ", 'polynomials':" ^ poly_string  ^ "}\n");
    F.print_flush();*)
    let simplified_constr =
    let string = call_Sage ("{'cmd':'reduceModulo', 'equations':" ^ gb_system ^ ", 'polynomials':" ^ poly_string  ^ "}\n") in
    (*
    F.printf "\n\n\n%s\n\n\n" string;
    F.print_flush();*)
    string
    |> String.filter ~f:(fun c -> c <> '\n')
    |> String.filter ~f:(fun c -> c <> ' ')
    |> String.filter ~f:(fun c -> c <> '"')
    |> string2gbpoly
    in
    let simplified_constr = 
      if L.length vars > 0 then
	L.hd_exn (constraints_of_groebner_polys simplified_constr sums vars qvars q_ineq)
      else
	constraint_of_poly
    in
    let rn2 = Ivar.Map.of_alist_exn (L.zip_exn new_ivars ivars) in
    rename_poly simplified_constr.poly rn2

(* End reduction *)

let filter_constraints_gb_rest constraints =
  let f c =
    c.is_eq = Eq && 
    Map.fold c.poly
       ~init:true
       ~f:(fun ~key:s ~data:_c b -> b && (rvars s.monom) = [] && (hvars s.monom) = [])
  in
  L.filter constraints ~f, L.filter constraints ~f:(fun c -> not (f c))

let filter_constraints_with_without_sums constraints =
  let f c =
    Map.fold c.poly
       ~init:true
       ~f:(fun ~key:s ~data:_c b -> b && (L.length s.ivars = 0) )
  in
  L.filter constraints ~f:(fun c -> not (f c)), L.filter constraints ~f

let poly2summations p =  (* Assume the poly is in uniform notation *)
  Map.fold p
     ~init:[]
     ~f:(fun ~key:s ~data:c l -> 
         let group = L.find l ~f:(fun (idxs,_,_) -> L.equal idxs s.ivars ~equal:equal_ivar) in
	 match group with
	 | None -> l @ [(s.ivars, s.i_ineq, mk_poly [(c, mk_sum [] [] s.monom)] )]
	 | Some (_,_,p) -> (L.filter l ~f:(fun (idxs,_,_) -> not(L.equal idxs s.ivars ~equal:equal_ivar) )) @
	                   [(s.ivars, s.i_ineq, SP.(p +! mk_poly [(c, mk_sum [] [] s.monom)]) )]
        )

let summations2poly summations =
  L.fold_left summations
   ~init:SP.zero
   ~f:(fun p' (idxs, ineq, p) ->
        let new_p = Map.fold p
                       ~init:SP.zero
                       ~f:(fun ~key:s ~data:c new_p ->
                          SP.(new_p +! mk_poly [(c, mk_sum (idxs@s.ivars) (ineq@s.i_ineq) s.monom)])
                          )
	in
        SP.(p' +! new_p)
      )

let simplify_sums_in_param_constr gb_constraints c = (* Assume c is in unif form *)
  let new_p = 
    L.map (poly2summations c.poly) 
     ~f:(fun (idxs, ineq, p) ->
       let ivars = c.qvars @ idxs in
       (idxs, ineq, simplify_poly_groebner_basis gb_constraints p ivars ineq)
     )
     |> summations2poly
  in
  mk_constr c.qvars c.q_ineq c.is_eq new_p

let split_poly_in_monomials p = (* Outputs a list of pairs (param_poly, monom) Assume there are no summations in poly *)
  Map.fold p
     ~init:[]
     ~f:(fun ~key:s ~data:c l ->
        let s_monom = mult_monom (rvars_monom s.monom) (hvars_monom s.monom) in
        let group = L.find l ~f:(fun (_, m) -> equal_monom m s_monom) in
	match group with
	| None -> l @ [(mk_poly [(c, mk_sum [] [] (params_monom s.monom))], s_monom)]
	| Some (p, _) -> (L.filter l ~f:(fun (_, m) -> not(equal_monom m s_monom) )) @
                      [(SP.(p +! (mk_poly [(c, mk_sum [] [] (params_monom s.monom))])), s_monom)]
        )
  
let simplify_sums_in_vars_constr gb_constraints c = (* Assume c is in unif form *)
  let new_p =
    L.map (poly2summations c.poly)
     ~f:(fun (idxs, ineq, p) ->
       let ivars = c.qvars @ idxs in
       let p' = L.fold_left (split_poly_in_monomials p)
	         ~init:SP.zero
                 ~f:(fun p' (poly_part, m) -> 
                    SP.(p' +! ((simplify_poly_groebner_basis gb_constraints poly_part ivars ineq) *!
				  (mk_poly [BI.one, mk_sum [] [] m])))
		    )
       in
       (idxs, ineq, p')
        )
        |> summations2poly
  in
  mk_constr c.qvars c.q_ineq c.is_eq new_p

let opening constraints =
  let constraints = uniform_bound constraints in
  let qvars = L.fold_left constraints
               ~init:[]
               ~f:(fun l c -> L.dedup (l @ c.qvars) ~compare:compare_ivar)
  in
  L.map constraints 
   ~f:(fun c -> 
     let p = L.fold_left qvars
              ~init:c.poly
	      ~f:(fun p i -> split_poly i p)
     in       
     mk_constr qvars c.q_ineq c.is_eq p)
  |> uniform_qvars_constraints
  |> uniform_bound

let simplify constraints =
  let constraints = clear_equations (uniform_bound (all_ivar_distinct_constr_conj constraints)) in
  let constraints = opening constraints in
  let gb_constraints, rest_constraints = filter_constraints_gb_rest constraints in
  let polys, sums, vars, qvars, q_ineq = groebner_polys gb_constraints in
  let simplified_polys = string2gbpoly (groebner_basis (gbpolys2string polys)) in
  let simplified_constraints = constraints_of_groebner_polys simplified_polys sums vars qvars q_ineq in
  let with_sums, without_sums = filter_constraints_with_without_sums simplified_constraints in
  let with_sums = L.map with_sums ~f:(simplify_sums_in_param_constr without_sums) in
  ((L.map rest_constraints ~f:(simplify_sums_in_vars_constr gb_constraints)) @ with_sums @ without_sums)
  |> uniform_bound  
  |> remove_canceled_params
  |> clear_equations
  |> L.dedup ~compare:(fun c1 c2 -> if (isomorphic_constr c1 c2) then 0 else compare_constr c1 c2)
  
(* ----------------------------------------------------------------------- *)
(* Simplification rules *)	   
(*
let pp_changes constraints new_constraints p1 link p2 qvars =
  let modified = L.filter (L.zip_exn constraints new_constraints)
		  ~f:(fun (c1,c2) -> (compare_constr c1 c2) <> 0) in
  if (L.length modified > 0) then
    let () =
      if qvars = [] then
	F.printf " Use equation:@\n   %a %s %a \n@\n To simplify:@\n" pp_poly p1 link pp_poly p2
      else
	F.printf " Use equation:@\n forall %a: %a %s %a \n@\n To simplify:@\n" (pp_list "," pp_ivar) qvars pp_poly p1 link pp_poly p2
    in
    L.iter modified
     ~f:(fun (c1,c2) -> F.printf "  # %a    ->@\n    %a@\n@\n" pp_constr c1 pp_constr c2)
  else ()
*)
(*			
(* We use the fact that 'a * par^d = b' is an equation *)
let simplify_param_poly (par : atom) (d : BI.t) (a : poly) (b : poly) (p : poly) =
  let rec aux pairs =
    if BI.compare (f_pairs BI.max pairs) d < 0 then pairs2poly pairs par
    else
      aux (L.map pairs
	    ~f:(fun (p',d') -> if BI.compare d' d >= 0 then
				 (SP.(p' *! b), BI.(d' -! d))
			       else
				 (SP.(p' *! a), d')
	       )
	  )
	  (* Must the group order be distinct from a? *)
  in
  aux (poly2pairs p par)
       
let simplify_param_constrs (par : atom) (qbound : bool) (d : BI.t) (a : poly) (b : poly) constraints qvars qineq =
  (*let () = F.printf "%a -> %b@\n" pp_atom par (known_not_null a constraints) in*)
  if (known_not_null a constraints) then
    if (equal_poly b SP.zero) then
      if (not qbound) then 
	subst constraints par SP.zero
      else 
	let new_constraints = subst_bound constraints par SP.zero in
	Set.fold (free_ivars_constr_conj constraints)
         ~init:new_constraints
	 ~f:(fun constrs i ->
	     if L.mem qineq ~equal:Ivar_Pair.equal (i, Set.choose_exn (ivars_atom par)) then constrs
	     else subst constrs (map_idx ~f:(fun _ -> i) par) SP.zero)
	     
    else
      if (not qbound) then
	let current = mk_constr qvars qineq Eq SP.((a *! (power_poly (of_a par) d)) -! b) in
        let new_constraints =
	  (L.map constraints
	    ~f:(fun c ->
		if isomorphic_constr c current then c
		(*else
		  if (L.length (poly2pairs c.poly par)) = 1 && c.is_eq = InEq then c*)
		  else
		    let (rn,_) = renaming_away_from (Ivar.Set.of_list qvars)
				 (Set.union (bound_ivars_poly c.poly)
					    (Ivar.Set.of_list c.qvars))
		    in
		    let c = rename_constr c rn in
		    mk_constr (c.qvars @ qvars) (c.q_ineq @ qineq) c.is_eq (simplify_param_poly par d a b c.poly)
	       )
	  )
	in
	(*pp_changes constraints new_constraints SP.((power_poly (of_a par) d) *! a) "=" b qvars;*)
	new_constraints
      else
	let current = mk_constr ((Set.to_list (ivars_atom par)) @ qvars) qineq Eq SP.((a *! (power_poly (of_a par) d)) -! b) in
	(L.map constraints
	  ~f:(fun c ->
	      if isomorphic_constr c current then c
	      else
		if (equal_poly a SP.one) && (BI.(equal d one)) then L.hd_exn (subst_bound [c] par b)
		else c
	     )
	)
  else
    constraints

let divide_by_par par c =
  let pairs = poly2pairs c.poly par in
  let minimum = f_pairs BI.min pairs in
  let new_poly = pairs2poly (L.map pairs ~f:(fun (p,d) -> (p, BI.(d -! minimum)) )) par in
  (*
  let () = if (BI.is_zero minimum) then ()
	   else F.printf " Division by %a^%s in %a@\n" pp_atom par (BI.to_string minimum) pp_constr c
  in
   *)
  mk_constr c.qvars c.q_ineq c.is_eq new_poly
	    
let use_param_equation (par : atom) (c : constr) (constraints : constr_conj) is_eq =
  let qbound = match par with
    | Param (_, Some i) -> L.mem c.qvars ~equal:equal_ivar i
    | _ -> false
  in
  match poly2pairs c.poly par with
  | (p,d) :: [] ->
     if is_eq = Eq then
       if not (BI.is_zero d) then
	 simplify_param_constrs par qbound d p SP.zero constraints c.qvars c.q_ineq
       else constraints
     else
       if (qbound) then constraints
       else L.map constraints ~f:(fun c -> divide_by_par par c)
  | (p,d) :: (p',d') :: [] ->
     if (BI.is_zero d') && (is_eq = Eq) then
       simplify_param_constrs par qbound d p (SP.opp p') constraints c.qvars c.q_ineq
     else if (BI.is_zero d) && (is_eq = Eq) then
       simplify_param_constrs par qbound d' p' (SP.opp p) constraints c.qvars c.q_ineq
     else constraints
  | _ -> constraints
	       	   
let simplify_params (constraints : constr_conj) =
  let rec aux output = function
    | [] -> output
    | c :: rest_c ->
       let f = (fun ~key:s ~data:_ l -> l @ (not_bound_sum_params s) ) in	   
       let param_list = Map.fold c.poly ~init:[] ~f
			|> L.dedup ~compare:compare_atom
       in
       let new_output = L.fold_left param_list
			 ~init:output
			 ~f:(fun output' p -> use_param_equation p c output' c.is_eq)
			|> clear_equations
       in
       let new_rest = L.fold_left param_list
                       ~init:rest_c
		       ~f:(fun rest p -> use_param_equation p c rest c.is_eq)
		      |> clear_equations
       in
       aux (new_output @ [c]) new_rest
  in
  aux [] constraints
*)

let simplify_vars_constr c v =  (* Let's think of this rule!!! *)
  let pairs = poly2pairs c.poly v in
  let minimum = f_pairs BI.min pairs in
  let new_poly =
    if (BI.compare minimum BI.zero) < 0 then c.poly
    else pairs2poly (L.map pairs ~f:(fun (p,d) -> (p, BI.(d -! minimum)) )) v in
  mk_constr c.qvars c.q_ineq c.is_eq new_poly

let simplify_vars (constraitns : constr_conj) =
  let rec aux output = function
    | [] -> output
    | c :: rest_c ->
       let f = (fun ~key:s ~data:_ l -> l @ (not_bound_sum_vars s) ) in
       let var_list = Map.fold c.poly ~init:[] ~f
		      |> L.dedup ~compare:compare_atom in
       let new_c = L.fold_left var_list
		    ~init:c
		    ~f:(fun c' v -> simplify_vars_constr c' v)
       in
       aux (output @ [new_c]) rest_c
  in
  aux [] constraitns
  |> remove_canceled_params
  |> clear_equations
 (*     
let simplify2 constraints =
  uniform_bound constraints
  |> clear_equations
  |> simplify_params
  |> clear_equations
*)
(* ----------------------------------------------------------------------- *)
(* Find contradictions *)	   

let q_violation c =
  let is_constant s =
    (s.ivars = []) && (s.i_ineq = []) && 
    not(L.exists (Map.to_alist s.monom) ~f:(fun (a,_) -> (is_hvar a) || (is_rvar a) || (is_param a)))
  in
  not(L.exists (Map.to_alist c.poly) ~f:(fun (s,_c) -> not (is_constant s))) && (c.is_eq = Eq) && not(equal_poly c.poly SP.zero)

let contradictions (constraints : constr_conj) =
  let f c = (equal_poly c.poly SP.zero && c.is_eq = InEq) ||
	    (known_not_null c.poly constraints && c.is_eq = Eq) ||
	    (q_violation c) ||
	    (L.mem constraints (mk_constr c.qvars c.q_ineq (if c.is_eq = Eq then InEq else Eq) c.poly)
	      ~equal:(isomorphic_constr)
	    )
  in
  L.exists constraints ~f

let contradictions_msg (constraints : constr_conj) =
  let f c = (equal_poly c.poly SP.zero && c.is_eq = InEq) ||
	    (known_not_null c.poly constraints && c.is_eq = Eq) ||
	    (q_violation c) ||
	    (L.mem constraints (mk_constr c.qvars c.q_ineq (if c.is_eq = Eq then InEq else Eq) c.poly)
	      ~equal:(isomorphic_constr)
	    )
  in
  match L.find constraints ~f with
    | None -> false, (mk_constr [] [] Eq SP.zero)
    | Some c -> true, c
      
(* ----------------------------------------------------------------------- *)
(* Overlap *)
	   
let smt_solver system =
  let result = call_z3 (system ^ "\n") in
  match result with
  | "true" -> true
  | "false" -> false
  | s -> failwith ("Communication with python failed, got ``"^s^"''")
	   
(* Computes m1/m2 for all possible combinaions of indices between them *)
let join_monomials m1 m2 =
  let indices1 = ivars_monom m1 in
  let indices2 = ivars_monom m2 in
  let (_,indices) = renaming_away_from indices2 indices1 in
  let idx_perms = nchoosek_perm (Set.to_list indices) (Set.length indices1) in
  let renamings = L.map idx_perms ~f:(fun l -> Ivar.Map.of_alist_exn (L.zip_exn (Set.to_list indices1) l)) in
  let renamings_m1 = L.map renamings ~f:(fun rn -> map_idx_monom ~f:(apply_renaming rn) m1) in
  let m2_inv = Map.map m2 ~f:(fun e -> BI.opp e) in
  let monomials = L.map renamings_m1 ~f:(fun m -> mult_monom m m2_inv) in
  L.dedup monomials ~compare:compare_monom

(* On input m_k [i1,...,in], outputs [(m_i1, [i2,...,in]), (m_i2, [i1,i3,...,in]), ...] *)
let use_one_index mon indices =  let rec aux output used = function
    | [] -> output
    | i :: rest ->
       let m = map_idx_monom ~f:(fun _ -> i) mon in
       aux (output @ [(m, used @ rest)]) (used @ [i]) rest
  in
  match (Set.length (ivars_monom mon)) with
  | 0 -> [(mon, indices)]
  | 1 -> aux [] [] indices
  | _ -> assert false

let mons_sets_product (mlist1 : monom list) (mlist2 : monom list) =
  L.concat_map mlist1 ~f:(fun m1 -> L.map mlist2 ~f:(fun m2 -> mult_monom m1 m2))
  |> L.dedup ~compare:compare_monom
		
let list2string (strings : string list) sep lim1 lim2 =
  lim1 ^ (String.concat ~sep strings) ^ lim2
	     
let matrix_row (a : atom) recur recur_idx =
  list2string (List.map (recur @ recur_idx) ~f:(fun x -> BI.to_string (degree a x))) ", " "[" "]"
	     
let smt_case_Mi mon (initial, idxs) k =
  let f m = let (vars,_) = L.unzip (rvars m) in vars in
  let variables = (f mon) @ (f initial)
		  |> L.dedup ~compare:compare_atom
  in
  let (matrix, vector) =
    L.fold_left variables ~init:([], [])
      ~f:(fun (mat,vec) v ->
	  let recur_idx = L.map k.recur_idx
			   ~f:(fun r -> L.map idxs
			                 ~f:(fun i -> map_idx_monom ~f:(fun _ -> i) r ))
			  |> L.concat
	  in
	  (mat @ [matrix_row v k.recur recur_idx],
	   vec @ [BI.(to_string ((degree v mon) -! (degree v initial)))] ) )
  in
  "\'{\\\"matrix\\\" : "   ^ (list2string matrix ", " "[" "]") ^
   ", \\\"vector\\\" : "   ^ (list2string vector ", " "[" "]") ^
   ", \\\"lambda\\\" : "   ^ (string_of_int (L.length k.recur)) ^
   ", \\\"indices\\\" : "  ^ (string_of_int (L.length idxs)) ^ "}\'"

let smt_case_MiMj mon (initial, idxs) i j k1 k2 =
  let f m = let (vars,_) = L.unzip (rvars m) in vars in
  let variables = (f mon) @ (f initial)
		  |> L.dedup ~compare:compare_atom
  in
  let (matrix, vector) =
    L.fold_left variables ~init:([], [])
      ~f:(fun (mat,vec) v ->
	  let recur_idx1 = L.map k1.recur_idx
			    ~f:(fun r -> L.map idxs
			                  ~f:(fun x -> if (equal_ivar x i) then (mk_monom [])
						       else map_idx_monom ~f:(fun _ -> x) r ))
			   |> L.concat
	  in
	  let recur_idx2 = L.map k2.recur_idx
			    ~f:(fun r -> L.map idxs
			                  ~f:(fun x -> if (equal_ivar x j) then (mk_monom [])
						       else map_idx_monom ~f:(fun _ -> x) r ))
			   |> L.concat
	  in
	  (mat @ [matrix_row v (k1.recur @ k2.recur) (recur_idx1 @ recur_idx2)],
	   vec @ [BI.(to_string ((degree v mon) -! (degree v initial)))] ) )
  in
  "\'{\\\"matrix\\\" : "   ^ (list2string matrix ", " "[" "]") ^
   ", \\\"vector\\\" : "   ^ (list2string vector ", " "[" "]") ^
   ", \\\"lambda\\\" : "   ^ (string_of_int (L.length (k1.recur @ k2.recur))) ^
   ", \\\"indices\\\" : "  ^ (string_of_int (L.length idxs)) ^ "}\'"
												 
let smt_system_Mi mon i k =
  let indices = Set.to_list (ivars_monom mon) in
  if (L.mem indices i) then String.Set.empty
  else
    let initials = L.concat (L.map k.non_recur ~f:(fun m -> use_one_index m indices)) in
    L.fold_left initials
     ~init:String.Set.empty	      
     ~f:(fun se (initial,idxs) ->
         Set.union se (String.Set.singleton (smt_case_Mi mon (initial,idxs) k)) )
     
let smt_system_MiMj mon i j k1 k2 =
  let indices = Set.to_list (ivars_monom mon) in
  if (equal_ivar i j) && (L.mem indices i) then String.Set.empty
  else
    let indices1 = L.filter (j :: indices) ~f:(fun x -> not (equal_ivar x i))
		  |> L.dedup ~compare:compare_ivar in
    let indices2 = L.filter (i :: indices) ~f:(fun x -> not (equal_ivar x j))
		   |> L.dedup ~compare:compare_ivar in
    let (init1,_) = L.unzip (L.concat (L.map k1.non_recur ~f:(fun m -> use_one_index m indices1))) in
    let (init2,_) = L.unzip (L.concat (L.map k2.non_recur ~f:(fun m -> use_one_index m indices2))) in
    let initials = mons_sets_product init1 init2 in
   (* print_list initials;*)
    let idxs_list = L.map initials ~f:(fun x -> Set.to_list (ivars_monom x)) in
    L.fold_left (L.zip_exn initials idxs_list)
     ~init:String.Set.empty
     ~f:(fun se (initial,idxs) ->
	Set.union se (String.Set.singleton (smt_case_MiMj mon (initial,idxs) i j k1 k2)) )
     
let monom_matches_hmonom m hm i_list k_list =
  let f mon =
    match i_list, k_list with
    | i :: [], k :: [] -> smt_system_Mi mon i k
    | i :: j :: [], k1 :: k2 :: [] -> smt_system_MiMj mon i j k1 k2
    | _ -> assert false
  in
  L.fold_left (join_monomials m hm)
   ~init:String.Set.empty
   ~f:(fun se mon -> Set.union se (f mon))

let system_handle_term m hm k1 k2 =
  let (rn,_) = renaming_away_from (ivars_monom hm) (ivars_monom m) in
  let m = map_idx_monom m ~f:(apply_renaming rn) in
  let handles_list =
    L.concat_map (hvars hm)
	    ~f:(fun (v,e) ->
            let v = match v with Hvar hv -> hv | _ -> assert false in
            if BI.is_one e then [v]
	    else if BI.(equal e (of_int 2)) then [v;v]
	    else failwith "Not supported")
  in
  match handles_list with
  | [h] ->
     begin match h.hv_gname with
     | G1 -> monom_matches_hmonom m (rvars_monom hm) [h.hv_ivar] [k1]
     | G2 -> monom_matches_hmonom m (rvars_monom hm) [h.hv_ivar] [k2]
     | Fp -> failwith "overlap: handle variable cannot be a field element"
     end     
  | [h1; h2] ->
     begin match h1.hv_gname, h2.hv_gname with
     | G1, G1 -> monom_matches_hmonom m (rvars_monom hm) [h1.hv_ivar; h2.hv_ivar] [k1; k1]
     | G2, G2 -> monom_matches_hmonom m (rvars_monom hm) [h1.hv_ivar; h2.hv_ivar] [k2; k2]
     | G1, G2 
     | G2, G1 -> monom_matches_hmonom m (rvars_monom hm) [h1.hv_ivar; h2.hv_ivar] [k1; k2]
     | _ -> failwith "overlap: handle variable cannot be a field element"
     end
  | _::_::_::_ | [] -> failwith "Not supported"
			   
let overlap m p k1 k2 =
  let handle_mons = L.filter (mons p) ~f:(fun m -> hvars m <> [])
		    |> L.dedup ~compare:compare_monom
  in
  let system = L.fold_left handle_mons
		~init:String.Set.empty
		~f:(fun se hm -> Set.union se (system_handle_term m hm k1 k2))
  in
  (* F.printf "%s\n\n\n" (list2string (Set.to_list system) ", " "\"[" "]\"");*)
  smt_solver (list2string (Set.to_list system) ", " "[" "]")

(* ----------------------------------------------------------------------- *)
(* stable terms *)
		  
let distinct_pairs idxs =
  let rec aux output = function
    | [] | _ :: [] -> output
    | i :: tl ->
       aux (L.fold_left tl ~init:output ~f:(fun l j -> l @ [(i,j)])) tl
  in
  aux [] idxs
	     
let extract_stable (eq : constr) (idxs, mon) k1 k2 =
  if (eq.is_eq = Eq) then
    if (overlap mon eq.poly k1 k2)
    then failwith (fsprintf "the monomial %a is not stable (overlap exists)" pp_monom mon) (* [eq] *)
    else
      let rvs = Atom.Map.of_alist_exn (rvars mon) in
      let free_ivars = Ivar.Set.diff (ivars_monom rvs) (Ivar.Set.of_list idxs) in
      let poly1 =
        Map.filter eq.poly
       	  ~f:(fun ~key:s_eq ~data:_c ->
              not (isomorphic_sum (mk_sum idxs [] rvs)
				  (mk_sum (Set.to_list (Ivar.Set.diff (ivars_monom (rvars_monom s_eq.monom)) free_ivars )) [] (rvars_monom s_eq.monom))
		   && hvars s_eq.monom = []))
      in
      let constr1 = mk_constr eq.qvars eq.q_ineq Eq poly1 in
      let constr2 = mk_constr (idxs@eq.qvars) ((distinct_pairs idxs)@eq.q_ineq) Eq (coeff eq.poly (idxs, mon)) in
      [ constr1; constr2 ]
  else
    failwith "impossible to extract terms from inequalities"

let extract_stable_nth constraints (idxs, mon) k1 k2 nth =
  let rec aux header tail n =
    if (n = 1) then header @ (extract_stable (L.hd_exn tail) (idxs, mon) k1 k2) @ (L.tl_exn tail)
    else aux (header @ [L.hd_exn tail]) (L.tl_exn tail) (n-1)
  in
  aux [] constraints nth
 
