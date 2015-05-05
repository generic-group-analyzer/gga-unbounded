(** Convert lexer and parser errors to ParseError exception *)
let wrap_error f s =
  let sbuf = Lexing.from_string s in
  try
    f sbuf
  with
  | Wlexer.Error msg ->
    failwith (Printf.sprintf "%s%!" msg)
  | Wparser.Error ->
    let start = Lexing.lexeme_start sbuf in
    let err = Printf.sprintf
                "Syntax error at offset %d (length %d): parsed ``%s'',\nerror at ``%s''"
                start
                (String.length s)
                (if start >= String.length s then s  else (String.sub s 0 start))
                (if start >= String.length s then "" else (String.sub s start (String.length s - start)))
    in
    print_endline err;
    failwith err
  | _ -> failwith "Unknown error while lexing/parsing."

(** Parse type declaration. *)
let constr = wrap_error (Wparser.constr Wlexer.lex)
