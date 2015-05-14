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
let chars = ['a'-'z' 'A'-'Z' '0'-'9']
		
rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | [' ' '\t']
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | ":"     { COLON }
  | ","     { COMMA }
  | "_"     { UNDERSCORE }
  | "@"     { AT }
  | "("     { LPAR }
  | ")"     { RPAR }
  | "*"     { STAR }
  | "+"     { PLUS }
  | "-"     { MINUS }
  | "^"     { HAT }
  | "="     { EQ }
  | "<>"    { NEQ }
	    
  | '-'?['0'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | "forall" { FORALL }
  | "sum"    { SUM }
  | ['i'-'l']chars* as s    { ID s}
  | ['r']chars* as s        { RVAR s}
  | ['p']chars* as s        { PARAM s}
  | ['h']chars* as s        { HVAR s}						    


and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
