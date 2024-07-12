(* Main function of the unbounded tool *)

open Core
open Abbrevs

let split_string_on_word string word =
  let n = String.length word in
  let rec aux k =
    if (k+n >= String.length string) then string, ""
    else if String.equal (String.sub string ~pos:k ~len:n) word then
      (String.sub string ~pos:0 ~len:k),
      (String.sub string ~pos:(k+n) ~len:((String.length string)-(k+n)) )
    else aux (k+1)
  in
  aux 0    

let input_file filename =
  let in_channel = In_channel.create filename in
  let rec go lines =
    match In_channel.input_line in_channel with
    | Some l ->
      go (l :: lines)
    | None -> lines
  in
  let lines = go [] in
  let _ = In_channel.close in_channel in
  String.concat ~sep:"\n" (L.rev lines)

let main =
  let argv = Sys.get_argv () in
  if Array.length argv <> 2 then
    Out_channel.output_string stderr (F.sprintf "usage: %s <scheme file>\n" argv.(0))
  else
    let definition, proof = split_string_on_word (input_file argv.(1)) "proof." in
    if String.is_empty proof then
      Analyze.automatic_prover definition
    else
      Analyze.analyze_unbounded definition proof
