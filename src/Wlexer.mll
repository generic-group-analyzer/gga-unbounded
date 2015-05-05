{
  open Wparser
  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")
  let unterminated_string () =
    raise (Error "unterminated string")

}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'

rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | [' ' '\t']
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | ":"     { COLON }
  | ","     { COMMA }
  | '-'?['0'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | "forall" { FORALL }
  | ['a'-'z' 'A'-'Z' ]
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']* as s
    { ID s }


and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
