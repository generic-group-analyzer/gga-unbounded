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

let system = [m_constr; s_constr]
let system = split {name = "k"; id = 0} system

let monomials = mons m_constr.poly

let rec list_element n = function
  | [] -> failwith "empty list"
  | hd :: tl -> if n = 1 then hd else list_element (n-1) tl
		   
let () =
  F.printf "%a" pp_constr_conj system ;
  F.printf "[%a]\n" (Util.pp_list ", " pp_monom) monomials ;
  F.printf "[%a]\n" (Util.pp_list ", " pp_monom) (mons_sets_product monomials  monomials) ;
  F.printf "%a" pp_poly (coeff m_constr.poly (list_element 4 monomials)) ;
