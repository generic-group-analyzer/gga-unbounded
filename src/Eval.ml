open Core
open Abbrevs
open Watom
open Wconstrs
open Wrules
open Util

(* ** FIXME : Get rid of this *)

let power_poly (p : poly) (e : BI.t) =
  let rec aux p' n = if BI.is_one n then p' else aux SP.(p' *! p) BI.(n -! one) in
  if BI.(compare e zero) < 0 then failwith "Not supported"
  else if BI.(compare e zero) = 0 then SP.one else aux p e

let rename_sum s rn =
  let ivars = L.map (unzip1 s.sum_ivarsK) ~f:(apply_renaming rn) in
  let isetsK = L.map (unzip2 s.sum_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn)) in
  let summand = map_idx_summand ~f:(apply_renaming rn) s.sum_summand in
  mk_sum (L.zip_exn ivars isetsK) summand

let rename_poly (p : poly) rn =
  Map.fold p.poly_map
     ~init:SP.zero
     ~f:(fun ~key:s ~data:c p' -> SP.(p' +! (mk_poly [(c,rename_sum s rn)]) ) )

let rename_constr c rn =
  let qvars = L.map (unzip1 c.constr_ivarsK) ~f:(apply_renaming rn) in
  let qsetsK = L.map (unzip2 c.constr_ivarsK) ~f:(fun set -> Ivar.Set.map set ~f:(apply_renaming rn)) in
  let poly = rename_poly c.constr_poly rn in
  mk_constr (L.zip_exn qvars qsetsK) c.constr_is_eq poly

let subst_sum (c : BI.t) (s : sum) (par : atom) qvars (value : poly) =
  let mon = (match s.sum_summand with | Mon(mon) -> mon | _ -> assert false) in
  let d = degree par mon in
  let s = mk_sum s.sum_ivarsK (Mon(mk_monom_of_map (Map.remove mon.monom_map par))) in
  let (rn,_) = renaming_away_from (Ivar.Set.of_list qvars) (ivars_poly value) in
  let new_value = rename_poly value rn in
  Map.fold (power_poly new_value d).poly_map ~init:(mk_poly [])
           ~f:(fun ~key:s' ~data:c' p -> SP.(p +! (mk_poly [(BI.(c *! c'), mult_sum s s')])))

(* not use this function with bound parameters *)
let subst (c : conj) (par : atom) (value : poly) =
  let subst_poly p qvars =
    Map.fold p.poly_map ~init:(mk_poly [])
                  ~f:(fun ~key:s ~data:c p -> SP.(p +! (subst_sum c s par qvars value)))
  in
  let new_constrs = 
    L.map c.conj_constrs
     ~f:(fun x -> mk_constr x.constr_ivarsK x.constr_is_eq (subst_poly x.constr_poly (unzip1 x.constr_ivarsK)))
  in
  mk_conj c.conj_ivarsK new_constrs


(* ** Interpreter state and utility functions
 * ----------------------------------------------------------------------- *)

type eval_state = {
  es_gs       : group_setting option;
  es_inputs   : (poly * group_name) list;
  es_varnames : string list;
  es_uvars    : atom list;

  es_odefs    : ((poly * group_name) list) option;  (* oracle return values *)
  es_oparams  : (string * ty) list;
  es_orvars   : atom list;

  es_mwcond   : conj option;
  es_lcombs   : (group_name * poly) list;
}

let empty_eval_state = {
  es_gs       = None;
  es_inputs   = [];
  es_varnames = [];
  es_uvars    = [];
  es_odefs    = None;
  es_oparams  = [];
  es_orvars   = [];
  es_mwcond   = None;
  es_lcombs   = [];
}

let fold_sum_monom (s : sum) ~f =
  match s.sum_summand with
  | Mon(mon) -> mk_sum s.sum_ivarsK (Mon(map_atom_monom ~f mon))
  | _ -> assert false

let uvar_to_param (s : sum) (v : atom) =
  let f ~key:k ~data:d m =
    let new_k = match k with
      | Uvar (name, idx) when String.equal name (atom_name v) -> Param(name, idx)
      | _ -> k
    in
    map_add_ignore_duplicate m ~key:new_k ~data:d
  in
  fold_sum_monom s ~f

let uvar_to_hvar (s : sum) (v : atom) (g : group_name) =
  let f ~key:k ~data:d m =
    let new_k = match k with
      | Uvar (name, oivar) when String.equal name (atom_name v) ->
        let ivar = Option.value ~default:{ name = "k"; id = 0; } oivar in
        Hvar { hv_name = name; hv_ivar = ivar; hv_gname = g }
      | _ -> k
    in
    map_add_ignore_duplicate m ~key:new_k ~data:d
  in
  fold_sum_monom s ~f

let uvars_sum (s : sum) =
  match s.sum_summand with
  | Mon(mon) -> unzip1 (uvars mon)
  | _ -> assert false

let used_uvars_poly p = Map.fold p.poly_map ~init:[] ~f:(fun ~key:s ~data:_ l -> l @ (uvars_sum s))

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
  if Option.is_some estate.es_odefs then
    failwith "Oracle already defined, multiple oracles not supported.";
  ensure_vars_defined used ovarnames

let ensure_winning_valid estate choices used =
  let names = estate.es_varnames @ L.map choices ~f:(fun (v,_) -> atom_name v) in
  if not (unique names ~equal:String.equal) then
    failwith "Winning condition reuses names.";
  ensure_vars_defined used (estate.es_varnames @ names)


(* ** Interpret add oracle
 * ----------------------------------------------------------------------- *)

let ipoly_to_opoly params p =
  let add_param p' (v,ty) =
     match ty with
     | Fp ->
       Map.fold p'.poly_map
         ~init:SP.zero
         ~f:(fun ~key:s ~data:c p''-> SP.(p'' +! mk_poly [(c, uvar_to_param s v)] ))
     | GroupName gid ->
       Map.fold p'.poly_map
         ~init:SP.zero
         ~f:(fun ~key:s ~data:c p''-> SP.(p'' +! mk_poly [(c, uvar_to_hvar s v gid)] ))
  in
  L.fold_left params ~init:p ~f:add_param

let interp_add_oracle params orvars fs estate =
  let varnames =
    estate.es_varnames @
    L.map orvars ~f:atom_name @
    L.map params ~f:(fun (v,_) -> atom_name v)
  in
  let used_vars = L.map (L.concat_map fs ~f:(fun (p,_) -> used_uvars_poly p)) ~f:atom_name in
  ensure_oracle_valid estate varnames used_vars;
  let od =
    Some (L.map fs ~f:(fun (p, gid) -> (ipoly_to_opoly params p,gid)))
  in
  if Option.is_some estate.es_odefs then failwith "At most one oracle definition supported";
  { estate with
    es_odefs    = od;
    es_oparams  = L.map params ~f:(fun (p,gid) -> (atom_name p,gid));
    es_orvars   = orvars;
    es_varnames = varnames }


(* ** Interpret winning condition
 * ----------------------------------------------------------------------- *)

let uvar_to_idxuvar (s : sum) (v : atom) (i : ivar) =
  let f ~key:k ~data:d m =
    let new_k = match k with
      | Uvar(name, None) when String.equal name (atom_name v) -> Uvar(name, Some i)
      | _ -> k
    in
    map_add_ignore_duplicate m ~key:new_k ~data:d
  in
  fold_sum_monom s ~f

let param_to_idxparam (s : sum) (par_name : string) (i : ivar) =
  let f ~key:k ~data:d m =
    let new_k = match k with
      | Param (name, None) when String.equal name par_name -> Param (name, Some i)
      | _ -> k
    in
    map_add_ignore_duplicate m ~key:new_k ~data:d
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
  let s = L.fold_left orvars ~init:s ~f:(fun s' var -> uvar_to_idxuvar s' var i) in
  let s = L.fold_left oparams
            ~init:s
            ~f:(fun s' (name,ty) ->
                  match ty with
                  | Fp -> param_to_idxparam s' name i
                  | _  -> s')
  in
  mk_sum (s.sum_ivarsK @ [(i, Ivar.Set.empty)]) s.sum_summand

let iconds_to_wconds conds choices estate =
  let trans_cond c =
    let new_poly =
      L.fold_left estate.es_oparams
        ~init:c.constr_poly
        ~f:(fun p (v,group) ->
              match group with
              | Fp ->
                Map.fold p.poly_map
                  ~init:SP.zero
                  ~f:(fun ~key:s ~data:c p ->
                        SP.(p +! mk_poly [(c, uvar_to_param s (Uvar (v, None)))] ))
              | GroupName(gid) ->
                Map.fold p.poly_map
                  ~init:SP.zero
                  ~f:(fun ~key:s ~data:c p ->
                        SP.(p +! mk_poly [(c, uvar_to_hvar s (Uvar (v,None)) gid)] )))
    in
    mk_constr c.constr_ivarsK c.constr_is_eq new_poly
  in
  let conds = L.map conds ~f:trans_cond in
  let (new_conds,_, lcombshapes) =
    L.fold_left choices
   ~init:(conds,estate,[])
   ~f:(fun (conds,estate,lcombshapes) choice ->
       match choice with
       | (v, Fp) ->
         let fp c =
           let new_poly =
             Map.fold c.constr_poly.poly_map
               ~init:SP.zero
               ~f:(fun ~key:s ~data:c p' -> SP.(p' +! mk_poly [(c, uvar_to_param s v)]) )
           in
           mk_constr c.constr_ivarsK c.constr_is_eq new_poly
         in
         (L.map conds ~f:fp,
          { estate with es_oparams = estate.es_oparams @ [(atom_name v, Fp)] },
         lcombshapes)
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
                              ~f:(fun p par -> SP.(p *! of_atom (Param (par,None)))) in
          let params2 = fresh_params (L.length outputs) (used_params @ params) in
          let lcomb_opts = L.map2_exn outputs params2
                            ~f:(fun p par ->
                              let sum_index = {name = "k"; id = 0 } in
                              Map.fold SP.(p *! of_atom (Param (par,Some sum_index))).poly_map
                                 ~init:SP.zero
                                 ~f:(fun ~key:s ~data:c p' -> SP.(p' +!
                                     mk_poly [(c, index_sum s sum_index estate.es_orvars estate.es_oparams)])                                                 )
                             ) in
          let new_term = L.fold_left (lcomb_inputs @ lcomb_opts)
                          ~init:SP.zero
                          ~f:(fun p lcomb -> SP.(p +! lcomb) ) in
          ((subst (mk_conj [] conds) v new_term).conj_constrs,
            { estate with es_oparams = estate.es_oparams @
                                       (L.map (params @ params2) ~f:(fun p -> (p,Fp))) },
          (gid, new_term) :: lcombshapes) )
  in
  new_conds, lcombshapes


(* ** Interpret experiment definition
 * ----------------------------------------------------------------------- *)

type cmd =
  | GroupSetting of group_setting
  | AddSamplings of atom list
  | AddInput     of poly list * group_name
  | AddOracle    of string * (atom * ty) list * (atom list) * (poly * group_name) list
  | SetWinning   of (atom * ty) list * conj

let eval_cmd estate cmd =
  match cmd,estate.es_mwcond with

  | GroupSetting(gs),None ->
    if Option.is_some estate.es_gs then
      failwith "Cannot set group setting, already set.";
    { estate with es_gs = Some gs }

  | AddSamplings(vars),None ->
    let varnames = L.map vars ~f:atom_name in
    ensure_vars_fresh varnames estate.es_varnames;
    { estate with es_uvars = estate.es_uvars @ vars; es_varnames = estate.es_varnames @ varnames }

  | AddInput(fs,gid), None ->
    let used_vars = L.concat (L.map fs ~f:(fun p -> used_uvars_poly p)) in
    let used_varnames = L.map used_vars ~f:atom_name in
    ensure_vars_defined used_varnames (L.map estate.es_uvars ~f:atom_name);
    { estate with
      es_varnames = L.dedup_and_sort ~compare:String.compare (estate.es_varnames @ used_varnames);
      es_inputs   = estate.es_inputs @ (L.map fs ~f:(fun p -> (p, gid)));
    }

  | AddOracle(_,params,orvars,fs), None ->
    interp_add_oracle params orvars fs estate

  | SetWinning(choices,conds), None ->
    let used_vars = L.map (L.concat_map conds.conj_constrs ~f:(fun c -> used_uvars_poly c.constr_poly)) ~f:atom_name in
    ensure_winning_valid estate choices used_vars;
    let wconstrs, lcombshapes = iconds_to_wconds conds.conj_constrs choices estate in
    { estate with es_mwcond = Some (mk_conj conds.conj_ivarsK wconstrs); 
                  es_lcombs = lcombshapes }

  | _, Some _ ->
    failwith "Setting the winning condition must be the last command."

(* ** Compute knowledge
 * ----------------------------------------------------------------------- *)

let knowledge estate =
  let add_index_to_orvars mon =
    Map.fold mon.monom_map
       ~init:Atom.Map.empty
       ~f:(fun ~key:k ~data:d m ->
           let new_k = match k with
             | Uvar (name, None) when L.mem estate.es_orvars k ~equal:Atom.equal ->
               Uvar (name, Some { name = "k"; id = 0 })
             | _ -> k
           in
           map_add_ignore_duplicate m ~key:new_k ~data:d)
    |> mk_monom_of_map
  in
  let update advMsets non_recur recur =
    let sm_glob = L.filter non_recur ~f:(fun m -> Set.length (ivars_monom m) = 0) in
    let sm_orcl = L.filter non_recur ~f:(fun m -> Set.length (ivars_monom m) > 0) in
    let tm_glob = L.filter recur ~f:(fun m -> Set.length (ivars_monom (uvars_monom m)) = 0) in
    let tm_orcl = L.filter recur ~f:(fun m -> Set.length (ivars_monom (uvars_monom m)) > 0) in
    { sm_glob = advMsets.sm_glob @ (L.map sm_glob ~f:mon2umon);
      sm_orcl = advMsets.sm_glob @ (L.map sm_orcl ~f:mon2umon);
      tm_glob = advMsets.sm_glob @ (L.map tm_glob ~f:mon2umon);
      tm_orcl = advMsets.sm_glob @ (L.map tm_orcl ~f:mon2umon);
    }
  in
  let uone = mk_monom [] |> mon2umon in
  let advMsets_init = { sm_glob = [ uone ]; sm_orcl = []; tm_glob = []; tm_orcl = []; } in
  let oracle_outputs = match estate.es_odefs with | Some od -> od | _ -> assert false in
  L.fold_left (estate.es_inputs @ oracle_outputs)
   ~init:(advMsets_init, advMsets_init)
   ~f:(fun (advMsets1, advMsets2) (p,group) ->
     let monomials = L.map (mons p) ~f:add_index_to_orvars in
     let non_recur = L.filter monomials ~f:(fun m -> L.length (hvars m) = 0) in
     let recur = L.filter monomials ~f:(fun m -> L.length (hvars m) > 0) in
     match group, estate.es_gs with
     | G1, _        -> (update advMsets1 non_recur recur, advMsets2)
     | G2, Some II  -> (update advMsets1 non_recur recur, update advMsets2 non_recur recur)
     | G2, Some III -> (advMsets1, update advMsets2 non_recur recur)
     | G2, _ -> failwith "G2 cannot be defined in Type I setting"
   )
  |> (fun (advMsets1, advMsets2) -> { g1 = advMsets1; g2 = advMsets2; })

let lcombs_g1g2 lcombs =
  L.fold_left lcombs
   ~init:(None, None)
   ~f:(fun (lcomb1, lcomb2) (gid, p) ->
       match gid with
       | G1 ->
         begin match lcomb1 with
           | None -> (Some p, lcomb2)
           | Some _ -> (lcomb1, lcomb2)
         end
       | G2 ->
         begin match lcomb2 with
           | None -> (lcomb1, Some p)
           | Some _ -> (lcomb1, lcomb2)
         end
     )

let eval_cmds cmds =
  let es = L.fold_left cmds ~init:empty_eval_state ~f:eval_cmd in
  match es.es_mwcond with
  | Some constraints -> constraints, knowledge es, (lcombs_g1g2 es.es_lcombs)
  | None             -> failwith "No winning constraints"


(* ** Interpret proof script
 * ----------------------------------------------------------------------- *)

type instr =
  | GoTo            of int
  | IntrCoeff       of umonom * int
  | Simplify
  | CaseDistinction of atom
  | Contradiction
  | Uniform
  | DivideByParam   of atom
  | UniformVars
  | AssureLaurent
  | SplitInFactors of int
  | SimplifyCoeffs
  | ExtractCoeffs

let eval_instr advK system nth instr =
  match instr with
  | GoTo(n) ->
    if (n >= 0 && n <= L.length system) then (system, n)
    else failwith "wrong identifier"

  | IntrCoeff(uM, n_eq) ->
    let n_eq = n_eq - 1 in
    let f conj =
      let bound_ivars = 
        Set.to_list (Set.filter (ivars_umonom uM) ~f:(fun i -> not(L.mem ~equal:equal_ivar (unzip1 conj.conj_ivarsK) i)))
      in
      let quant = maximal_quant (unzip1 conj.conj_ivarsK) [] bound_ivars in
      let new_constrs = introduce_coeff (L.nth_exn conj.conj_constrs n_eq) quant uM (conj.conj_ivarsK) in
      mk_conj conj.conj_ivarsK (conj.conj_constrs @ new_constrs)
    in
    (list_map_nth system nth f, nth)

  | Simplify ->
    (list_map_nth system nth (simplify advK), nth)

  | CaseDistinction(par) ->
    let par =
      match par with
      | Uvar(name, None)   -> Param(name, None)
      | Uvar(name, Some i) -> Param(name, Some i)
      | _ -> assert false
    in
    let cases,_ = case_distinction (L.nth_exn system (nth-1) ) par in
    let case1 = L.nth_exn cases 0 in
    let case2 = L.nth_exn cases 1 in
    (L.concat (list_map_nth (L.map system ~f:(fun c -> [c])) nth (fun _ -> [case1] @ [case2])), nth)

  | Contradiction ->
    begin match contradiction (L.nth_exn system (nth-1)) with
      | None -> failwith "Contradiction not found"
      | Some _ -> (list_remove system nth, 1)
    end
    
  | Uniform ->
    (list_map_nth system nth opening, nth)

  | DivideByParam(a) ->
    let par =
      match a with
      | Uvar(name, None)   -> Param(name, None)
      | Uvar(name, Some i) -> Param(name, Some i)
      | _ -> assert false
    in
    let f conj = let (conj',_) = divide_conj_by par conj in conj' in
    (list_map_nth system nth f, nth)

  | UniformVars  ->
    (list_map_nth system nth uniform_vars, nth)

  | AssureLaurent ->
    let new_cases = assure_laurent_polys (L.nth_exn system (nth-1)) in
    if L.is_empty new_cases then failwith "New constraints were not found after applying 'assure_Laurent'"
    else
      (L.concat (list_map_nth (L.map system ~f:(fun c -> [c])) nth (fun _ -> new_cases)), nth)

  | SplitInFactors(n_eq) ->
    let n_eq = n_eq - 1 in
    let conj = L.nth_exn system (nth-1) in
    let new_cases =
      let c = L.nth_exn conj.conj_constrs n_eq in
      let other_constrs = L.filter conj.conj_constrs ~f:(fun c' -> not (equal_constr c c')) in
      L.map (split_in_factors conj.conj_ivarsK c ) ~f:(fun c' -> mk_conj conj.conj_ivarsK (c' :: other_constrs))
    in
    (L.concat (list_map_nth (L.map system ~f:(fun c -> [c])) nth (fun _ -> new_cases)), nth)

  | SimplifyCoeffs ->
    (list_map_nth system nth (simplify_coeff_conj advK), nth)

  | ExtractCoeffs ->
    let f conj =
      let conj, msgs = introduce_coeff_everywhere advK false conj in
      print_messages 0 msgs;
      conj
    in
    (list_map_nth system nth f, nth)

let eval_instrs instrs advK system nth =
  L.fold_left instrs
    ~init:(system,nth)
    ~f:(fun (system,nth) instr -> eval_instr advK system nth instr)
