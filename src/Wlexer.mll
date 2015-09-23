{
  open Wparser
  open Watom
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
  | "forall" { FORALL }
  | "sum"    { SUM }
  | "_"      { UNDERSCORE }
  | "'"      { QUOTE }
  | "group_setting" { GROUPSETTING }

  | "return" { RETURN }
  | "input"  { INP }
  | "oracle" { ORACLE }
  | "win"    { WIN }
  | "in"     { IN }

  | "extract"  { EXTRACT }
  | "case_distinction"  { CASE_DIST }
  | "goto"     { GOTO }
  | "admit"    { ADMIT }
  | "contradiction" { CONTRADICTION }
  | "uniform" { UNIFORM }
  | "simplify" { SIMPLIFY }
  | "simplify_vars" { SIMPLIFYVARS }

  | "G1"             { GROUP(G1) }
  | "G2"             { GROUP(G2) }

  | "Fp"             { FIELD }
  | ['o']chars* as s { ONAME s }

  | '-'?['0'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | ['i'-'m']chars* as s         { ID s}
  | chars* as s                  { RVAR s}

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
