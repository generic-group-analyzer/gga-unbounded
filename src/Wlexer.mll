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
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | "."     { DOT }
  | "("     { LPAR }
  | ")"     { RPAR }
  | "="     { EQ }
  | "->"    { TO }
  | "/\\"   { LAND }
  | "<>"    { INEQ }
  | "+"     { PLUS }
  | "-"     { MINUS }
  | "*"     { STAR }
  | "^"     { EXP } 
  | "["     { LBRACK }
  | "]"     { RBRACK }
  | ","     { COMMA }
  | ";"     { SEMICOLON }
  | ":"     { COLON }
  | "sample" { SAMP }
  | "maps"   { EMAPS }
  | "map"    { EMAPS }
  | "isos"   { ISOS }
  | "iso"    { ISOS }
  | "forall" { FORALL }
  | "sum"    { SUM }
  | "_"      { UNDERSCORE }

  | "return" { RETURN }
  | "input"  { INP }
  | "oracle" { ORACLE }
  | "win"    { WIN }
  | "in"     { IN }

  | "extract"  { EXTRACT }
  | "case_distinction"  { CASE_DIST }
  | "goto"     { GOTO }
  | "admit"    { ADMIT }
  | "simplify" { SIMPLIFY }

  | ['G']chars* as s { GROUP (String.sub s 1 (String.length s - 1)) }
  | "Fp"             { FIELD }
  | ['o']chars* as s { ONAME s }
					   
  | '-'?['0'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | ['i'-'j']chars* as s         { ID s}
  | chars* as s                  { RVAR s}

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
