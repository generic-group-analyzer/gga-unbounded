(* Main function of the unbounded tool *)

open Core_kernel.Std
open Abbrevs

let split_string_on_word string word =
  let n = String.length word in
  let rec aux k =
    if (k+n >= String.length string) then string, ""
    else if (String.sub string ~pos:k ~len:n) = word then
      (String.sub string ~pos:0 ~len:k),
      (String.sub string ~pos:(k+n) ~len:((String.length string)-(k+n)) )
    else aux (k+1)
  in
  aux 0    

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
  if Array.length Sys.argv <> 2 then
    output_string stderr (F.sprintf "usage: %s <scheme file>\n" Sys.argv.(0))
  else
    let definition, proof = split_string_on_word (input_file Sys.argv.(1)) "proof." in
    if proof = "" then
      assert false
    else
      Analyze.analyze_unbounded definition proof
