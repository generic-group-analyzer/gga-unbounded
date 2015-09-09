(* Main function of the unbounded tool *)

open Core_kernel.Std
open Abbrevs

let input_file filename =
  let in_channel = open_in filename in
  let rec go lines =
    try
      let l = input_line in_channel in
      go (l :: lines)
    with
      End_of_file -> lines
  in
  let lines = go [] in
  let _ = close_in_noerr in_channel in
  String.concat ~sep:"\n" (L.rev lines)
       
let main =
  if Array.length Sys.argv <> 3 then
    output_string stderr (F.sprintf "usage: %s <definition_file> <instructions_file / 'automatic'> \n" Sys.argv.(0))
  else
    let scmds = input_file Sys.argv.(1) in
    if Sys.argv.(2) = "automatic" then
      let filename = String.prefix Sys.argv.(1) ((String.length Sys.argv.(1)) - 4) in
      Analyze.automatic_tool scmds (filename ^ ".prf")
    else
      let instrs = input_file Sys.argv.(2) in
      Analyze.analyze_unbounded scmds instrs
