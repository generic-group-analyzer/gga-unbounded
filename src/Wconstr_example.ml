open Core.Std
open Abbrevs
open Watom
open Wconstrs

(* Example:
   Public key: [V,W]_1
   Sign([hm]_2) = [R, hm*V + W + R^2]_2,
   Win([m,r,s]_2) = forall i. m <> hm_i /\ s = m*V + W + r^2
*)


(* global random vars *)
let rV = mk_rvar "V"
let rW = mk_rvar "W"


(* Oracle *)
let i = { name = "i"; id = 0 }
let j = { name = "j"; id = 0 }
let hm i = mk_hvar ~idx:i "m"
let rR (i : ivar) = mk_rvar ~idx:(Some i) "R"

let lincomb idx p1 p2 p3 =
  SP.(
    let p1 = of_a p1 in
    let p2_j = of_a (p2 idx) in
    let p3_j = of_a (p3 idx) in
    let rV = of_a rV in
    let rW = of_a rW in
    let rR_j = of_a (rR idx) in
    let hm_j = of_a (hm idx) in

    p1 +!
    sum [idx] (p2_j *! rR_j) +!
    sum [idx] (p3_j *! (hm_j *! rV +! rW +! (rR_j *! rR_j)))
  )

let pm   = mk_param "pm"
let pmR i = mk_param ~idx:(Some i) "pmR"
let pmS i = mk_param ~idx:(Some i) "pmS"
let wm = lincomb j pm pmR pmS

let hm_spoly i = SP.of_a (hm i)

let m_constr = mk_constr [i] InEq SP.(wm -! hm_spoly i)
let m_constr = mk_constr [i] InEq SP.(wm -! SP.of_a (pmR i))
				       
let ps   = mk_param "ps"
let psR i = mk_param ~idx:(Some i) "psR"
let psS i = mk_param ~idx:(Some i) "psS"
let ws = lincomb j ps psR psS

let pr   = mk_param "pr"
let prR i = mk_param ~idx:(Some i) "prR"
let prS i = mk_param ~idx:(Some i) "prS"
let wr = lincomb j pr prR prS

let s_constr =
  let rV = SP.of_a rV in
  let rW = SP.of_a rW in
  mk_constr [] Eq SP.((wr *! wr) +! (wm *! rV) +! rW -! ws)


let unit_monom = mk_monom []
let k1 = {h = []; n = [unit_monom]; r =[]; rj =[]}
let k2 = {h = [hm i]; n = [unit_monom; (mk_monom [(NoInv,rR i)]) ; (mk_monom [(NoInv,rW)])];
	  r =[(mk_monom [(NoInv,rV)])]; rj =[]}

let system = [m_constr]
(*let system = [m_constr] @ (stable s_constr (mk_sum [] (mk_monom [(NoInv,rW)])) k1 k2)*)
(*let system = split {name = "k"; id = 0} system *)
	   
let monomials = mons m_constr.poly

		     
let _n = overlap (List.nth_exn monomials 0) (mult_monom (List.nth_exn monomials 1) (List.nth_exn monomials 1)) k1 k2

		 
let () =
  F.printf "%a" pp_constr_conj system ;
  let system2 = subst system pm (SP.(one)) in
  F.printf "%a" pp_constr_conj system2 ;
  let system3 = subst_bound_by_zero system (pmR j) in
  F.printf "%a" pp_constr_conj system3 ;
  (*
  F.printf "[%a]\n" (Util.pp_list ", " pp_monom) monomials ;
  F.printf "[%a]\n" (Util.pp_list ", " pp_monom) (mons_sets_product monomials  monomials) ;
  F.printf "%a\n" pp_poly (coeff m_constr.poly (List.nth_exn monomials 3)) ;
   *)
