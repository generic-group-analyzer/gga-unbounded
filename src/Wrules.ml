open Core.Std
open Util
open Abbrevs
open Watom
open Wconstrs

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

						   
let coeff_term c s mon =
  if (equal_monlist (rvars s.monom) (rvars mon)) &&
     (equal_monlist (hvars s.monom) (hvars mon))
  then mk_poly [(c, mk_sum s.ivars [] (params_monom s.monom))]
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
(* Substitute free occurence of index variable *)

let subst_idx_sum (i : ivar) (j : ivar) (s : sum) =
  if L.mem s.ivars i
  then failwith "subst_idx_sum: cannot substitute Sum-bound index variable bound"
  else mk_sum s.ivars s.i_ineq (map_idx_monom ~f:(fun x -> if x = i then j else x) s.monom)
	   
let subst_idx_poly (i : ivar) (j : ivar) (p : poly) =
  Map.fold p
    ~init:(mk_poly [])
	  ~f:(fun ~key:s ~data:c p -> SP.(p +! (mk_poly [(c, subst_idx_sum i j s)])))
	   	   
let subst_idx_constr (i : ivar) (j : ivar) (c : constr) =
  if L.mem c.qvars i
  then failwith "subst_idx_sum: impossible to substitute a summation variable"
  else mk_constr c.qvars c.q_ineq c.is_eq (subst_idx_poly i j c.poly)
		 
let rm_from_pairs (i : ivar) (pairs : ivar_pair list) =  
  L.filter pairs ~f:(fun (x,y) -> x <> i && y <> i)

let keep_from_pairs (i : ivar) (pairs : ivar_pair list) =
  L.filter pairs ~f:(fun (x,y) -> x = i || y = i)
	   
(* ----------------------------------------------------------------------- *)
(* Split forall and sum quantification as follows:
   split(i', forall i. e) = split(i',e)[i -> i'] /\ (forall i. (split(i',e)))
   split(i', sum i. e) = split(i',e)[i -> i'] + (sum i. (split(i',e)))
*)

let split_sum (iv : ivar) (sum : sum) =
  let rec do_split s =
    match s.ivars with      
    | [] -> [s]
    | i::is ->
       let (i_pairs, rest_pairs) = (keep_from_pairs i s.i_ineq), (rm_from_pairs i s.i_ineq) in       
       let sums = do_split (mk_sum is rest_pairs s.monom) in       
       let sums1 = L.map ~f:(fun s -> mk_sum (i::s.ivars) i_pairs s.monom) sums in       
       let sums2 = L.map ~f:(subst_idx_sum i iv) sums in       
       sums1 @ sums2		 
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
    | [] -> [ mk_constr [] [] c.is_eq (split_poly iv c.poly) ]
    | i::is ->
      let constrs = do_split (mk_constr is (rm_from_pairs i c.q_ineq) c.is_eq c.poly) in
      let constrs1 = L.map ~f:(fun c -> mk_constr (i::c.qvars) c.q_ineq c.is_eq c.poly) constrs in
      let constrs2 = L.map ~f:(subst_idx_constr i iv) constrs in
      constrs1 @ constrs2
  in
  if L.mem constr.qvars iv
  then failwith (fsprintf "split_constr: given index variable %a not fresh" pp_ivar iv)
  else do_split constr
       
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

let extract_stable (eq : constr) (s : sum) k1 k2 =
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
      let constr1 = mk_constr [] [] Eq poly1 in
      let constr2 = mk_constr s.ivars [] Eq (coeff eq.poly ([],s.monom)) in
      [ constr1; constr2 ]
  ) else ( [eq] )

(* ----------------------------------------------------------------------- *)
(* Case distinctions *)
(*
let remove_forall (c : constr) =
  mk_constr (L.filter c.qvars ~f:(fun x -> L.mem (Ivar.Set.to_list (ivars_constr c)) x )) c.is_eq c.poly
    
let power_poly (p : poly) (e : BI.t) =
  let rec aux p' n = if BI.is_one n then p' else aux SP.(p' *! p) BI.(n -! one) in
  if BI.(compare e zero) < 0 then failwith "Not suported"
  else if BI.(compare e zero) = 0 then SP.one else aux p e 
						       
let subst_sum (c : BI.t) (s : sum) (par : atom) (value : poly) =
  let d = degree par s.monom in
  let s = mk_sum s.ivars (Map.remove s.monom par) in
  Map.fold (power_poly value d) ~init:(mk_poly [])
	   ~f:(fun ~key:s' ~data:c' p -> SP.(p +! (mk_poly [(BI.(c *! c'), mult_sum s s')])))
	   
(* not use this function with bound parameters *)
let subst (c : constr_conj) (par : atom) (value : poly) =
  let subst_poly p =
    Map.fold p ~init:(mk_poly [])
		  ~f:(fun ~key:s ~data:c p -> SP.(p +! (subst_sum c s par value)))
  in
  List.map c ~f:(fun x -> mk_constr x.qvars x.is_eq (subst_poly x.poly))

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
  let subst_poly p qvars =
    Map.fold p ~init:(mk_poly [])
	    ~f:(fun ~key:s ~data:c p -> SP.(p +! (subst_bound_sum c s qvars par)))
  in
  List.map c
    ~f:(fun x -> remove_forall (mk_constr x.qvars x.is_eq (subst_poly x.poly x.qvars)))
 
 *)
