open Core.Std
open Abbrevs
open Wconstrs

(* Example:
   Public key: [V,W]_1
   Sign([hm]_2) = [R, hm*V + W + R^2]_2,
   Win([m,r,s]_2) = forall i. m <> hm_i /\ s = m*V + W + r^2
*)

(* global random vars *)
let rV = rvar "V"
let rW = rvar "W"

(* Oracle *)
let i = "i"
let j = "i"
let hm i = hvar "m" i
let rR i = rvar_idx "R" i

let lincomb p1 p2 p3 =
  { sum =
      L.map
        ~f:(fun e -> (BI.one,e))
        [ ssum []  { prod = [p1] };
          ssum [j] { prod = [p2 j; rR j] };
          ssum [j] { prod = [p3 j; hm j; rV] };
          ssum [j] { prod = [p3 j; rW] };
          ssum [j] { prod = [p3 j; rR j; rR j] }; ] }

let pm1   = param "pm1"
let pm2 i = param_idx "pm2" i
let pm3 i = param_idx "pm3" i
let wm = lincomb pm1 pm2 pm3

let ps1   = param "ps1"
let ps2 i = param_idx "ps2" i
let ps3 i = param_idx "ps3" i
let ws = lincomb ps1 ps2 ps3

let pr1   = param "pr1"
let pr2 i = param_idx "pr2" i
let pr3 i = param_idx "pr3" i
let wr = lincomb ps1 ps2 ps3

(* FIXME: define multiplication to make this work *)
let s_constr () =
  let rV = spoly_of_smonom [rV] in
  let rW = spoly_of_smonom [rW] in
  constr [] Eq SP.((wr *! wr) +! (ws *! rV) +! rW -! ws)

let hm_spoly i = spoly_of_smonom [hm i]

let m_constr = constr [i] InEq SP.(wm -! hm_spoly i)

let () =
  F.printf "%a" pp_constr m_constr
