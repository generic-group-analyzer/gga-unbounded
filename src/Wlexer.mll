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

  | "goto"             { GOTO }
  | "coeff"            { COEFF }
  | "simplify"         { SIMPLIFY }
  | "case_distinction" { CASE_DIST }
  | "contradiction"    { CONTRADICTION }
  | "uniform_ivars"    { UNIFORM }
  | "divide_by_param"  { DIVIDE_PARAM }
  | "uniform_vars"     { UNIFORM_VARS }
  | "assure_Laurent"   { ASSURE_LAURENT }
  | "clear_independent_eqs"   { CLEAR_INDP_EQS }
  | "split_in_factors" { SPLIT_IN_FACTORS }
  | "simp_Coeff"       { SIMPLIFY_COEFFS }
  | "extract_coeffs"   { EXTRACT_COEFFS }

  | "G1"             { GROUP(G1) }
  | "G2"             { GROUP(G2) }

  | "Fp"             { FIELD }
  | ['o']chars* as s { ONAME s }

  | '-'?['0'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | ['i'-'l']chars* as s         { ID s}
  | chars* as s                  { UVAR s}

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
