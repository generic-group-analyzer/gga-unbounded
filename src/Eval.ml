open Core_kernel.Std
open Abbrevs
open Watom
open Wconstrs
open Wrules
open Util

(* ** Interpreter state and utility functions
 * ----------------------------------------------------------------------- *)

type eval_state = {
  es_gs       : group_setting option;
  es_inputs   : (poly * group_name) list;
  es_varnames : string list;
  es_rvars    : atom list;

  es_odefs    : ((poly * group_name) list) option;  (* oracle return values *)
  es_oparams  : (string * ty) list;
  es_orvars   : atom list;

  es_mwcond   : constr_conj option;
}

let empty_eval_state = {
  es_gs       = None;
  es_inputs   = [];
  es_varnames = [];
  es_rvars    = [];
  es_odefs    = None;
  es_oparams  = [];
  es_orvars   = [];
  es_mwcond   = None;
}

let atom_to_name = function
  | Uvar (name, _) -> name
  | Param (name,_) -> name
  | Hvar hv        -> hv.hv_name
  | Nqueries _     -> failwith "impossible: unexpected Nqueries constructor"

let fold_sum_monom (s : sum) ~f =
  mk_sum s.ivars s.i_ineq (Map.fold s.monom ~init:Atom.Map.empty ~f)

let rvar_to_param (s : sum) (v : atom) =
  let f ~key:k ~data:d m =
    let new_k = match k with
      | Uvar (name, idx) when name = atom_to_name v -> Param(name, idx)
      | _ -> k
    in
    Map.add m ~key:new_k ~data:d
  in
  fold_sum_monom s ~f

let rvar_to_hvar (s : sum) (v : atom) (g : group_name) =
  let f ~key:k ~data:d m =
    let new_k = match k with
      | Uvar (name, oivar) when name = atom_to_name v ->
        let ivar = Option.value ~default:{name = "_k"; id = 0} oivar in
	Hvar { hv_name = name; hv_ivar = ivar; hv_gname = g }
      | _ -> k
    in
    Map.add m ~key:new_k ~data:d
  in
  fold_sum_monom s ~f

let vars_s s = let (vars,_) = L.unzip (rvars s.monom) in vars

let used_vars_p p = Map.fold p ~init:[] ~f:(fun ~key:s ~data:_ l -> l @ (vars_s s))

(* ** Well-formedness checking
 * ----------------------------------------------------------------------- *)

let ensure_vars_fresh fresh used =
  L.iter fresh
   ~f: (fun var -> if L.mem ~equal:String.equal used var then
		     failwith (fsprintf "sampled variable %s not fresh" var))

let ensure_vars_defined used defined =
  L.iter used
   ~f: (fun var -> if not (L.mem ~equal:String.equal defined var) then
		     failwith (fsprintf "used variable %s undefined (add sample X)" var))

let ensure_oracle_valid estate ovarnames used =
  if not (unique ovarnames ~equal:String.equal) then
    failwith "Oracle reuses names for arguments/sampled variables.";
  if estate.es_odefs <> None then
    failwith "Oracle already defined, multiple oracles not supported.";
  ensure_vars_defined used ovarnames

let ensure_winning_valid estate choices used =
  let names = estate.es_varnames @ L.map choices ~f:(fun (v,_) -> atom_to_name v) in
  if not (unique names ~equal:String.equal) then
    failwith "Winning condition reuses names.";
  ensure_vars_defined used (estate.es_varnames @ names)


(* ** Interpret add oracle
 * ----------------------------------------------------------------------- *)

let ipoly_to_opoly params p =
  let add_param p' (v,ty) =
     match ty with
     | Fp ->
       Map.fold p'
         ~init:SP.zero
	 ~f:(fun ~key:s ~data:c p''->
	       SP.(p'' +! mk_poly [(c, rvar_to_param s v)] ))
     | GroupName gid ->
       Map.fold p'
         ~init:SP.zero
	 ~f:(fun ~key:s ~data:c p''-> SP.(p'' +! mk_poly [(c, rvar_to_hvar s v gid)] ))
  in
  L.fold_left params ~init:p ~f:add_param

let interp_add_oracle params orvars fs estate =
  let varnames =
    estate.es_varnames @
    L.map orvars ~f:atom_to_name @
    L.map params ~f:(fun (v,_) -> atom_to_name v)
  in
  let used_vars = L.map (L.concat_map fs ~f:(fun (p,_) -> used_vars_p p)) ~f:atom_to_name in
  ensure_oracle_valid estate varnames used_vars;
  let od =
    Some (L.map fs ~f:(fun (p, gid) -> (ipoly_to_opoly params p,gid)))
  in
  if estate.es_odefs <> None then failwith "At most one oracle definition supported";
  { estate with
    es_odefs    = od;
    es_oparams  = L.map params ~f:(fun (p,gid) -> (atom_to_name p,gid));
    es_orvars   = orvars;
    es_varnames = varnames }


(* ** Interpret winning condition
 * ----------------------------------------------------------------------- *)

let rvar_to_irvar (s : sum) (v : atom) (i : ivar) =
  let f ~key:k ~data:d m =
    let new_k = match k with
      | Uvar(name, None) when name = atom_to_name v -> Uvar(name, Some i)
      | _                                           -> k
    in
    Map.add m ~key:new_k ~data:d
  in
  fold_sum_monom s ~f

let param_to_iparam (s : sum) (par_name : string) (i : ivar) =
  let f ~key:k ~data:d m =
    let new_k = match k with
      | Param (name, None) when name = par_name -> Param (name, Some i)
      | _                                       -> k
    in
    Map.add m ~key:new_k ~data:d
  in
  fold_sum_monom s ~f

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
  let s = L.fold_left orvars ~init:s ~f:(fun s' var -> rvar_to_irvar s' var i) in
  let s = L.fold_left oparams
	    ~init:s
	    ~f:(fun s' (name,ty) ->
	          match ty with
	          | Fp -> param_to_iparam s' name i
	          | _  -> s')
  in
  mk_sum (i::s.ivars) s.i_ineq s.monom

let iconds_to_wconds conds choices estate =
  let trans_cond c =
    let new_poly =
      L.fold_left estate.es_oparams
        ~init:c.poly
	~f:(fun p (v,group) ->
	      match group with
	      | Fp ->
		Map.fold p
		  ~init:SP.zero
		  ~f:(fun ~key:s ~data:c p ->
                        SP.(p +! mk_poly [(c, rvar_to_param s (Uvar (v, None)))] ))
	      | GroupName(gid) ->
		Map.fold p
		  ~init:SP.zero
		  ~f:(fun ~key:s ~data:c p ->
		        SP.(p +! mk_poly [(c, rvar_to_hvar s (Uvar (v,None)) gid)] )))
    in
    mk_constr c.qvars c.q_ineq c.is_eq new_poly
  in
  let conds = L.map conds ~f:trans_cond in
  let (new_conds,_) =
    L.fold_left choices
   ~init:(conds,estate)
   ~f:(fun (conds,estate) choice ->
       match choice with
       | (v, Fp) ->
	 let fp c =
	   let new_poly =
             Map.fold c.poly
	       ~init:SP.zero
	       ~f:(fun ~key:s ~data:c p' -> SP.(p' +! mk_poly [(c, rvar_to_param s v)]) )
	   in
	   mk_constr c.qvars c.q_ineq c.is_eq new_poly
	 in
	 (L.map conds ~f:fp,
	  { estate with es_oparams = estate.es_oparams @ [(atom_to_name v, Fp)] } )
       | (v, GroupName gid) ->
	  let (inputs,_) = L.filter estate.es_inputs ~f:(fun (_,g) -> equal_group_name g gid)
			  |> L.unzip in
	  let outputs = match estate.es_odefs with
	    | Some od -> let (out,_) = L.filter od ~f:(fun (_,g) -> equal_group_name g gid)
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
			      let sum_index = {name = "_k"; id = 0 } in
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


(* ** Interpret experiment definition
 * ----------------------------------------------------------------------- *)

type cmd =
  | GroupSetting of group_setting
  | AddSamplings of atom list
  | AddInput     of poly list * group_name
  | AddOracle    of string * (atom * ty) list * (atom list) * (poly * group_name) list
  | SetWinning   of (atom * ty) list * constr_conj

let eval_cmd estate cmd =
  match cmd,estate.es_mwcond with

  | GroupSetting(gs),None ->
    if estate.es_gs <> None then
      failwith "Cannot set group setting, already set.";
    { estate with es_gs = Some gs }

  | AddSamplings(vars),None ->
    let varnames = L.map vars ~f:atom_to_name in
    ensure_vars_fresh varnames estate.es_varnames;
    { estate with es_rvars = estate.es_rvars @ vars; es_varnames = estate.es_varnames @ varnames }

  | AddInput(fs,gid), None ->
    let used_vars = L.concat (L.map fs ~f:used_vars_p) in
    let used_varnames = L.map used_vars ~f:atom_to_name in
    ensure_vars_defined used_varnames (L.map estate.es_rvars ~f:atom_to_name);
    { estate with
      es_varnames = L.dedup ~compare:String.compare (estate.es_varnames @ used_varnames);
      es_inputs   = estate.es_inputs @ (L.map fs ~f:(fun p -> (p, gid)));
    }

  | AddOracle(_,params,orvars,fs), None ->
    interp_add_oracle params orvars fs estate

  | SetWinning(choices,conds), None ->
    let used_vars = L.map (L.concat_map conds ~f:(fun c -> used_vars_p c.poly)) ~f:atom_to_name in
    ensure_winning_valid estate choices used_vars;
    { estate with es_mwcond = Some (iconds_to_wconds conds choices estate) }

  | _, Some _ ->
    failwith "Setting the winning condition must be the last command."

(* ** Compute knowledge
 * ----------------------------------------------------------------------- *)

let knowledge estate =
  let auxiliary mon =
    Map.fold mon
       ~init:Atom.Map.empty
       ~f:(fun ~key:k ~data:d m ->
	   let new_k = match k with
	     | Uvar (name, None) when L.mem estate.es_orvars k ~equal:Atom.equal ->
		Uvar (name, Some { name = "_k"; id = 0 })
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
       | G1, _        -> (update_k k1 non_recur recur recur_idx, k2)
       | G2, Some II  -> (update_k k1 non_recur recur recur_idx, update_k k2 non_recur recur recur_idx)
       | G2, Some III -> (k1, update_k k2 non_recur recur recur_idx)
       | G2, Some I   -> failwith "G2 encountered for Type I"
       | G2, None     -> (k1, update_k k2 non_recur recur recur_idx)
      )

let eval_cmds cmds =
  let es = L.fold_left cmds ~init:empty_eval_state ~f:eval_cmd in
  match es.es_mwcond with
  | Some constraints -> uniform_bound constraints, knowledge es
  | None             -> failwith "No winning constraints"


(* ** Interpret proof script
 * ----------------------------------------------------------------------- *)

type instr =
  | Extract         of (ivar list * monom) * int
  | CaseDistinction of atom
  | GoTo            of int
  | Admit
  | Uniform
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
      | Uvar(name, None) -> Param(name, None)
      | Uvar(name, Some i) -> Param(name, Some i)
      | _ -> failwith "eval_instr: input should be a random variable"
    in
    let cases = (case_dist (L.nth_exn system (nth-1) ) par) in
    let case1 = (*simplify*) clear_non_used_idxs (L.nth_exn cases 0) in
    let case2 = (*simplify*) clear_non_used_idxs (L.nth_exn cases 1) in
    (L.concat (list_map_nth (L.map system ~f:(fun c -> [c])) nth (fun _ -> [case1] @ [case2])), nth)

  | GoTo(n) ->
    if (n >= 0 && n <= L.length system) then (system, n)
    else failwith "wrong identifier"

  | Admit ->
    (list_remove system nth, 1)

  | Uniform ->
    (list_map_nth system nth uniform_bound, nth)

  | Simplify ->
    (list_map_nth system nth simplify, nth)

  | SimplifyVars ->
    (list_map_nth system nth (fun constrs -> (*simplify*) (simplify_vars constrs)), nth)

let eval_instrs instrs (k1,k2) system nth =
  L.fold_left instrs
    ~init:(system,nth)
    ~f:(fun (system,nth) instr -> eval_instr (k1,k2) system nth instr)
