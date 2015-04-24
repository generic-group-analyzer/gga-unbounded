open Core.Std
(* open Core_sexp *)
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
let idx = "i"
let hm = hvar "m" idx 
let rR = rvar_idx "R" idx

let mu1 = param "mu1"
let mu2 = param "mu2"
let mu3 = param "mu3"

let wm =
  { sum =
      [ ssum 1 []    { prod = [mu1] };
        ssum 1 [idx] { prod = [mu2; rR] };
        ssum 1 [idx] { prod = [mu3; hm; rV] };
        ssum 1 [idx] { prod = [mu3; rW] };
        ssum 1 [idx] { prod = [mu3; rR; rR] }; ] }

let () =
  if compare_spoly wm wm = 0 then
    print_string (Sexp.to_string_hum ~indent:2 (sexp_of_spoly wm))
