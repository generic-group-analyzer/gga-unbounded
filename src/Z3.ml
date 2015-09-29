module YS = Yojson.Safe

(* Set the env variable UBT_PATH *)
let z3_script = Format.sprintf "python %s/smt_solver.py" (Sys.getenv "UBT_PATH")

type st_z3 = {
  mutable sts_closed : bool;
  sts_cin    : in_channel;
  sts_cout   : out_channel;
}

let persistent_z3 = ref None

let start_z3 () =
  let (c_in, c_out) = Unix.open_process z3_script in
  { sts_cin = c_in; sts_cout = c_out; sts_closed = false }

let eval_z3 sts cmd =
  if sts.sts_closed then failwith "z3 process already closed";
  let (c_in, c_out) = sts.sts_cin, sts.sts_cout in
  (*i print_endline (">>> sent "^cmd); i*)
  output_string c_out cmd;
  flush c_out;
  (*i print_endline (">>> wait "); i*)
  let res = input_line c_in in
  (*i print_endline (">>> got "^res); i*)
  res

let stop_z3 sts =
  if sts.sts_closed then failwith "z3 process already closed";
  let (c_in, c_out) = sts.sts_cin, sts.sts_cout in
  let cmd = YS.to_string (`Assoc [ ("cmd",`String "exit") ])^"\n" in
  output_string c_out cmd;
  flush c_out;
  let o = input_line c_in in
  if o <> "end" then failwith "close: end expected";
  ignore (Unix.close_process (c_in,c_out))

let call_z3 cmd =
  match !persistent_z3 with
  | None ->
    let sts = start_z3 () in
    persistent_z3 := Some sts;
    eval_z3 sts cmd
  | Some sts ->
    eval_z3 sts cmd
