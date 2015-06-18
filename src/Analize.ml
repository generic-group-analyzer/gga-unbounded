open Abbrevs
open Wconstrs
open Watom

let analyze_unbounded cmds instrs =
  let file = open_out "log" in
  let shell = Unix.dup Unix.stdout in
  Unix.dup2 (Unix.descr_of_out_channel file) Unix.stdout;
  let constraints, (k1,k2) = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let (system, nth) = Eval.eval_instrs (Wparse.p_instrs instrs) (k1,k2) [constraints] 1 in
  F.print_flush ();
  close_out file;
  Unix.dup2 shell Unix.stdout;
  
  if (L.length system = 0) then
    F.printf "Proven!\n(Group order >= %d)@\n" (Big_int.int_of_big_int !group_order_bound)

  else
    let constraints = L.nth_exn system (nth-1) in
    F.printf "\nWorking on goal %d out of %d." nth (L.length system);  
    F.printf "%s(Group order >= %d)@\n\n" ("       ") (Big_int.int_of_big_int !group_order_bound);
    F.printf "%a" pp_constr_conj constraints;
    if Wrules.contradictions constraints then
      print_string "Contradiction!\n\n"
    else ()
