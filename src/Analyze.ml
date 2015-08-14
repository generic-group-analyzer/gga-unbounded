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
    F.printf "# Proven!\n(Group order >= %d)@\n" (Big_int.int_of_big_int !group_order_bound)

  else
    let constraints = L.nth_exn system (nth-1) in
    F.printf "Working on goal %d out of %d." nth (L.length system);  
    F.printf "%s(Group order >= %d)@\n\n" ("       ") (Big_int.int_of_big_int !group_order_bound);
    F.printf "%a" pp_constr_conj constraints;
    let (contradiction, c) = Wrules.contradictions_msg constraints in
    if contradiction then
      F.printf "Contradiction!\n%a" pp_constr c
    else ()


let analyze_unbounded_ws cmds instrs =
  let open Big_int in
  let constraints, (k1,k2) = Wparse.p_cmds cmds |> Eval.eval_cmds in
  let (system, nth) = Eval.eval_instrs (Wparse.p_instrs instrs) (k1,k2) [constraints] 1 in

  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  begin match system with
  | [] ->
    F.fprintf fbuf "<p>Proven!\n(Group order >= %s)\n</p>" (string_of_big_int !group_order_bound)
  | _::_ ->
    let constraints = L.nth_exn system (nth-1) in
    F.fprintf fbuf 
       "<p>Working on goal %d out of %d.  (Group order >= %s)</p>\n"
       nth (L.length system) (string_of_big_int !group_order_bound);  
    F.fprintf fbuf "%a" PPLatex.pp_constr_conj_latex constraints;
    let (contradiction, c) = Wrules.contradictions_msg constraints in
    if contradiction then
      let () = F.fprintf fbuf "\n<p>Contradiction!\n</p>" in
      F.fprintf fbuf "<p><script type=\"math/tex\" mode=\"display\">%a\n</script></p>" PPLatex.pp_constr_latex c
    else ()
  end;
  F.pp_print_flush fbuf ();
  Buffer.contents buf
