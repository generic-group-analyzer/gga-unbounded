open Core.Std
open Abbrevs
open Watom
open Wconstrs
open Wrules
open Util
 
       
type cmd =
  | AddMaps      of (string * string) list
  | AddIsos      of (string * string) list
  | AddSamplings of atom list
  | AddInput     of poly list * string
  | AddOracle    of string * (atom * string) list * (atom list) * (poly * string) list
  | SetWinning   of (atom * string) list * constr_conj
					     
type eval_state = {
  es_gs       : group_setting option * string * string;
  es_inputs   : (poly * group_name) list;
  es_varnames : string list;
  es_rvars    : atom list;
  es_odefs    : ((poly * group_name) list) option;
  es_oparams  : (string * group_name) list;
  es_orvars   : atom list;
  es_mwcond   : constr_conj option;
}

let empty_eval_state = {
  es_gs       = (None, "", "");
  es_inputs   = [];
  es_varnames = [];
  es_rvars    = [];
  es_odefs    = None;
  es_oparams  = [];
  es_orvars   = [];
  es_mwcond   = None;
}

let ensure_vars_fresh fresh used =
  L.iter fresh
   ~f: (fun var -> if L.mem ~equal:String.equal used var then
		     failwith (fsprintf "sampled variable %s not fresh" var))

let ensure_vars_defined used defined =
  L.iter used
   ~f: (fun var -> if not (L.mem ~equal:String.equal defined var) then
		     failwith (fsprintf "used variable %s undefined (add sample X)" var))
   
let atom2name = function
  | Rvar (name, _) -> name
  | Param (name,_) -> name
  | Hvar hv -> hv.hv_name
  | _ -> ""

let ensure_oracle_valid estate ovarnames used =
  if not (unique ovarnames ~equal:String.equal)
  then
    failwith "Oracle reuses names for arguments/sampled variables.";
  if estate.es_odefs <> None
  then
    failwith "Oracle already defined, multiple oracles not supported.";
  ensure_vars_defined used ovarnames
		
let ensure_winning_valid estate choices used =
  let names = estate.es_varnames @ L.map choices ~f:(fun (v,_) -> atom2name v) in
  if not (unique names ~equal:String.equal) then failwith "Winning condition reuses names.";
  ensure_vars_defined used (estate.es_varnames @ names)
							  
let classify_gname es_gs gname =
  match es_gs with
  | (_,g1,g2) -> if String.equal gname g1 then G1
		 else if String.equal gname g2 then G2
		 else if String.equal gname "Fp" then Fp
		 else failwith (fsprintf "%s is not a source group" gname)

let map_rvar s ~f =
  mk_sum s.ivars s.i_ineq (Map.fold s.monom ~init:Atom.Map.empty ~f)

let rvar2param s v =
  let f = fun ~key:k ~data:d m ->
    let new_k = match k with
      | Rvar (name, idx) when String.equal name (atom2name v) -> Param(name, idx)
      | _ -> k
    in 
    Map.add m ~key:new_k ~data:d
  in
  map_rvar s ~f
	   
let rvar2hvar s v g =
  let f = fun ~key:k ~data:d m ->
    let new_k = match k with
      | Rvar (name, Some i) when String.equal name (atom2name v) ->
	 Hvar { hv_name = name; hv_ivar = i; hv_gname = g }
      | Rvar (name, None) when String.equal name (atom2name v) ->
	 Hvar { hv_name = name; hv_ivar = {name = "k"; id = 0}; hv_gname = g }
      | _ -> k
    in
    Map.add m ~key:new_k ~data:d
  in
  map_rvar s ~f
	   
let rvar2irvar s v i =
  let f = fun ~key:k ~data:d m ->
    let new_k = match k with
      | Rvar (name, None) when String.equal name (atom2name v) ->
	 Rvar (name, Some i)
      | _ -> k
    in
    Map.add m ~key:new_k ~data:d
  in
  map_rvar s ~f
	 
let param2iparam s par_name i =
  let f = fun ~key:k ~data:d m ->
    let new_k = match k with
      | Param (name, None) when String.equal name par_name->
	 Param (name, Some i)
      | _ -> k
    in
    Map.add m ~key:new_k ~data:d
  in
  map_rvar s ~f
	   
let ipoly_to_opoly es_gs params p =
  L.fold_left params
   ~init:p
   ~f:(fun p' (v,gname) ->
       if String.equal gname "Fp" then
	 Map.fold p'
	    ~init:SP.zero
	    ~f:(fun ~key:s ~data:c p''->
		SP.(p'' +! mk_poly [(c, rvar2param s v)] ))
       else
	 Map.fold p'
	    ~init:SP.zero
	    ~f:(fun ~key:s ~data:c p''->
		SP.(p'' +! mk_poly [(c, rvar2hvar s v (classify_gname es_gs gname))] ))
      )

let fresh_params n used =
  let rec go k used =
    let p = "p" ^ (string_of_int k) in
    if (L.mem used p ~equal:String.equal) then go (k+1) used
    else p
  in
  let rec aux output n used =
    if (n = 0) then output
    else
      let p = go 1 used in
      aux (output @ [p]) (n-1) (p :: used)
  in
  aux [] n used

let index_sum s i orvars oparams =
  let s = L.fold_left orvars
	     ~init:s
	     ~f:(fun s' var -> rvar2irvar s' var i)
  in
  let s = L.fold_left oparams
	   ~init:s	      
	   ~f:(fun s' (name,group) ->
	       match group with
	       | Fp -> param2iparam s' name i
	       | _ -> s'
	      )
  in
  mk_sum (i::s.ivars) s.i_ineq s.monom
      
let iconds_to_wconds conds choices estate =
  let conds = L.map conds
	       ~f:(fun c ->
		   let new_poly =
		     L.fold_left estate.es_oparams
                      ~init:c.poly
		      ~f:(fun p' (v,group) ->
			  match group with
			  | Fp -> 
			    Map.fold p'
			        ~init:SP.zero
				~f:(fun ~key:s ~data:c p''->
				    SP.(p'' +! mk_poly [(c, rvar2param s (Rvar (v, None)))] ))
			  | _ ->
			    Map.fold p'
				~init:SP.zero
				~f:(fun ~key:s ~data:c p''->
				    SP.(p'' +! mk_poly [(c, rvar2hvar s (Rvar (v,None)) group)] ))
			 )
		   in
		   mk_constr c.qvars c.q_ineq c.is_eq new_poly
		  )
  in
  let (new_conds,_) =
    L.fold_left choices
   ~init:(conds,estate)
   ~f:(fun (conds,estate) choice ->
       match choice with
       | (v, "Fp") ->
	  let fp = (fun c -> 
	       let new_poly = Map.fold c.poly
				 ~init:SP.zero
				 ~f:(fun ~key:s ~data:c p' -> SP.(p' +! mk_poly [(c, rvar2param s v)]) )
	       in
	       mk_constr c.qvars c.q_ineq c.is_eq new_poly
	      )
	  in
	  (L.map conds ~f:fp,
	  { estate with es_oparams = estate.es_oparams @ [(atom2name v, Fp)] } )
       | (v, gname) ->
	  let gid = classify_gname estate.es_gs gname in
	  let (inputs,_) = L.filter estate.es_inputs ~f:(fun (_,g) -> compare_group_name g gid = 0)
			  |> L.unzip in
	  let outputs = match estate.es_odefs with
	    | Some od -> let (out,_) = L.filter od ~f:(fun (_,g) -> compare_group_name g gid = 0)
				       |> L.unzip in
			 out
	    | None -> []
	  in
	  let used_params = (L.map estate.es_oparams ~f:(fun (p,_) -> p)) in
	  let params = fresh_params ((L.length inputs)+1) used_params in
	  let lcomb_inputs = L.map2_exn (SP.one :: inputs) params
			      ~f:(fun p par -> SP.(p *! of_a (Param (par,None)))) in
	  let params2 = fresh_params (L.length outputs) (used_params @ params) in
	  let lcomb_opts = L.map2_exn outputs params2
			    ~f:(fun p par ->
			      let sum_index = {name = "k"; id = 0 } in
			      Map.fold SP.(p *! of_a (Param (par,Some sum_index)))
				 ~init:SP.zero
				 ~f:(fun ~key:s ~data:c p' -> SP.(p' +!
				     mk_poly [(c, index_sum s sum_index estate.es_orvars estate.es_oparams)])                                                 )		   
			     ) in
	  let new_term = L.fold_left (lcomb_inputs @ lcomb_opts)
			  ~init:SP.zero
			  ~f:(fun p lcomb -> SP.(p +! lcomb) ) in
	  (subst conds v new_term,
	    { estate with es_oparams = estate.es_oparams @
				       (L.map (params @ params2) ~f:(fun p -> (p,Fp))) } ) )
  in
  new_conds
							  
let eval_cmd estate cmd =
  let vars_s s = let (vars,_) = L.unzip (rvars s.monom) in vars in
  let used_vars_p p = Map.fold p ~init:[] ~f:(fun ~key:s ~data:_ l -> l @ (vars_s s)) in
  match cmd,estate.es_mwcond with
  | AddMaps(emaps),None ->
     begin match emaps with
     | (g1,g2) :: [] ->
	{ estate with es_gs = ((if String.equal g1 g2 then Some I else Some III),g1,g2) }
     | _ -> failwith "only one bilinear map supported"
     end
       
  | AddIsos(isos),None ->
     begin match isos,estate.es_gs with
     | (g_from, g_to) :: [], (Some gs_type,g1,g2) ->
	if not (L.mem ~equal:String.equal [g1;g2] g_from) || not (L.mem ~equal:String.equal [g1;g2] g_to) then
	  failwith "eval_cmd: wrong isomorphism, unknown groups"
	else		
	  if (gs_type = III) then { estate with es_gs = (Some II, g_to, g_from) }
	  else estate
     | _, (None,_,_) -> failwith "undefined bilinear map"
     | _,_ -> failwith "only one isomorphism supported"
     end
       
  | AddSamplings(vars),None ->
     let varnames = L.map vars ~f:atom2name in
     ensure_vars_fresh varnames estate.es_varnames;
     { estate with es_rvars = estate.es_rvars @ vars; es_varnames = estate.es_varnames @ varnames }
      
  | AddInput(fs,gname), None ->
     let gid = classify_gname estate.es_gs gname in
     let used_vars = L.concat (L.map fs ~f:used_vars_p) in
     ensure_vars_defined (L.map used_vars ~f:atom2name) (L.map estate.es_rvars ~f:atom2name);
     { estate with
       es_varnames = (estate.es_varnames @ (L.map used_vars ~f:atom2name))     
		     |> L.dedup ~compare:String.compare;
       es_inputs = estate.es_inputs @ (L.map fs ~f:(fun p -> (p, gid)));
     }
     
  | AddOracle(_,params,orvars,fs), None ->
    let varnames =
      estate.es_varnames @ (L.map orvars ~f:atom2name) @ L.map params ~f:(fun (v,_) -> atom2name v)
    in
    let used_vars = L.map (L.concat (L.map fs ~f:(fun (p,_) -> used_vars_p p))) ~f:atom2name in
    ensure_oracle_valid estate varnames used_vars;
    let od =
      Some (L.map fs ~f:(fun (p, gname) ->
		   (ipoly_to_opoly estate.es_gs params p,
		    (classify_gname estate.es_gs gname))) )
    in
    if estate.es_odefs <> None then failwith "At most one oracle definition supported";
    { estate with
      es_odefs    = od;
      es_oparams  = L.map params ~f:(fun (p,gname) -> (atom2name p, (classify_gname estate.es_gs gname)));
      es_orvars   = orvars;
      es_varnames = varnames }
      
  | SetWinning(choices,conds), None ->
     let used_vars = L.map (L.concat (L.map (L.map conds ~f:(fun c -> c.poly )) ~f:used_vars_p)) ~f:atom2name in
     ensure_winning_valid estate choices used_vars;
     { estate with es_mwcond = Some (iconds_to_wconds conds choices estate) }
       
  | _, Some _ ->
    failwith "Setting the winning condition must be the last command."

let knowledge estate =
  let auxiliary mon =
    Map.fold mon
       ~init:Atom.Map.empty
       ~f:(fun ~key:k ~data:d m ->
	   let new_k = match k with
	     | Rvar (name, None) when L.mem estate.es_orvars k ~equal:Atom.equal ->
		Rvar (name, Some { name = "k"; id = 0 })
	     | _ -> k
	   in
	   Map.add m ~key:new_k ~data:d)
  in  
  let update_k k non_recur recur recur_idx =
    { non_recur = L.dedup (k.non_recur @ non_recur) ~compare:compare_monom;
      recur     = L.dedup (k.recur @ recur)         ~compare:compare_monom;
      recur_idx = L.dedup (k.recur_idx @ recur_idx) ~compare:compare_monom }
  in
  let k_init = { non_recur = [mk_monom []]; recur = []; recur_idx = [] } in
  let ooutputs = match estate.es_odefs with | Some od -> od | _ -> assert false in
  L.fold_left (estate.es_inputs @ ooutputs)
   ~init:(k_init, k_init)
   ~f:(fun (k1,k2) (p,group) ->
       let monomials = L.map (mons p) ~f:auxiliary in
       let non_recur = L.filter monomials ~f:(fun m -> L.length (hvars m) = 0) in
       let recur =
	 L.filter monomials
	  ~f:(fun m -> (Set.length (ivars_monom (rvars_monom m)) = 0) && (L.length (hvars m) > 0))
	 |> L.map ~f:(fun m -> rvars_monom m)
       in
       let recur_idx =
	 L.filter monomials
	  ~f:(fun m -> (Set.length (ivars_monom (rvars_monom m)) > 0) && (L.length (hvars m) > 0))
	 |> L.map ~f:(fun m -> rvars_monom m)
       in
       match group, estate.es_gs with
       | G1,_ -> (update_k k1 non_recur recur recur_idx, k2)
       | G2, (Some gs,_,_) ->
	  if (compare_group_setting gs II) = 0 then
	    (update_k k1 non_recur recur recur_idx, update_k k2 non_recur recur recur_idx)
	  else
	    (k1, update_k k2 non_recur recur recur_idx)
       | G2,_ -> (k1, update_k k2 non_recur recur recur_idx)
       | Fp,_ -> (k1,k2)
      )
   	     
let eval_cmds cmds =
  let es =  L.fold_left cmds ~init:empty_eval_state ~f:eval_cmd in
  match es.es_mwcond with
  | Some constraints -> constraints, (knowledge es)
  | None -> failwith "No winning constraints"

type instr =
  | Extract         of (ivar list * monom) * int
  | CaseDistinction of atom
  | GoTo            of int
  | Admit
  | Simplify
  | SimplifyVars

let eval_instr (k1,k2) system nth instr =
  match instr with
  | Extract((idxs,mon), n) ->
     let f constraints = extract_stable_nth constraints (idxs,mon) k1 k2 n
		         (*|> simplify*)
     in
     (list_map_nth system nth f, nth)
		  
  | CaseDistinction(par) ->
     let par =
       match par with
       | Rvar(name, None) -> Param(name, None)
       | Rvar(name, Some i) -> Param(name, Some i)
       | _ -> failwith "eval_instr: input should be a random variable"
     in
     let cases = (case_dist (L.nth_exn system (nth-1) ) par) in
     let case1 = (*simplify*) (L.nth_exn cases 0) in
     let case2 = (*simplify*) (L.nth_exn cases 1) in
     ((list_map_nth system nth (fun _ -> case1)) @ [case2], nth)

  | GoTo(n) ->
     if (n >= 0 && n <= L.length system) then (system, n)
     else failwith "wrong identifier"

  | Admit ->
     (list_remove system nth, 1)

  | Simplify ->
     (list_map_nth system nth simplify, nth)

  | SimplifyVars ->
     (list_map_nth system nth (fun constrs -> (*simplify*) (simplify_vars constrs)), nth)

let eval_instrs instrs (k1,k2) system nth =
  L.fold_left instrs
   ~init:(system,nth)
   ~f:(fun (system,nth) instr -> eval_instr (k1,k2) system nth instr)
