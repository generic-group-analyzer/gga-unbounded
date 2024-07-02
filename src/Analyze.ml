open Core
open Abbrevs
open Heuristic
   
let automatic_prover cmds =
  let conj, advK, lcombs = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let t1 = Core_unix.gettimeofday() in
  let proven = call_heuristic conj advK lcombs in
  let t2 = Core_unix.gettimeofday() in
  if proven then
    let () = F.printf "Proven!\nTime %F seconds\n" (Stdlib.ceil ((100.0 *. (t2 -. t1))) /. 100.0) in
    exit 0
  else
    let () = F.printf "Not proven!\nTime: %F seconds\n" (Stdlib.ceil ((100.0 *. (t2 -. t1))) /. 100.0) in
    exit 1    

let analyze_unbounded cmds instrs =
  let conj, advK, _ = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let (branches, nth) = Eval.eval_instrs (Wparse.p_instrs instrs) advK [conj] 1 in

  if (L.length branches = 0) then
    F.printf "Proven!\n"
  else
    let conj = L.nth_exn branches (nth-1) in
    F.printf "Working on goal %d out of %d.\n" nth (L.length branches);
    F.printf "%a" WconstrsUtil.pp_conj conj;
    ()

let string_of_state st =
  let (branches, nth) = st in
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  begin match branches with
  | [] ->
    F.fprintf fbuf "<p>Proven!\n\n</p>"
  | _::_ ->
    let conj = L.nth_exn branches (nth-1) in
    F.fprintf fbuf
       "<p>Working on goal %d out of %d.</p>\n" nth (L.length branches);
    F.fprintf fbuf "%a" PPLatex.pp_conj_latex conj;
   ()
  end;
  F.pp_print_flush fbuf ();
  Buffer.contents buf
