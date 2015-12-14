%{
  open Wconstrs
  open Watom
  open Util
  open Abbrevs
  open Eval
%}

%token EOF
%token DOT
%token COMMA
%token IN
%token COLON
%token LAND
%token GROUPSETTING

%token LBRACK
%token RBRACK
%token LPAR
%token RPAR

%token EQ
%token INEQ
%token SAMP
%token SEMICOLON
%token UNDERSCORE
%token FORALL
%token SUM

%token INP
%token ORACLE
%token WIN
%token RETURN

%token STAR
%token PLUS
%token MINUS
%token EXP

%token <Watom.group_name> GROUP
%token FIELD

%token <int> INT
%token <string> ID

%token <string> UVAR
%token <string> ONAME


%token GOTO
%token COEFF
%token SIMPLIFY
%token CASE_DIST
%token CONTRADICTION
%token UNIFORM
%token DIVIDE_PARAM
%token UNIFORM_VARS
%token ASSURE_LAURENT
%token CLEAR_INDP_EQS
%token SPLIT_IN_FACTORS
%token SIMPLIFY_COEFFS

%token QUOTE

/************************************************************************/
/* Priority & associativity */

/* Multiplication has the highest precedence. */
%left PLUS MINUS
%left STAR

/************************************************************************/
/* Production types */

%type <Eval.cmd list> cmds_t
%type <Eval.instr list> instrs_t

/************************************************************************/
/* Start productions */

%start cmds_t
%start instrs_t

%%

/************************************************************************/
/* Types */

ivar :
| idx = ID                    { { name = idx; id = 0 } }
| idx = ID; QUOTE;            { { name = idx; id = 1 } }
| idx = ID; QUOTE; n = INT    { if n > 0 then { name = idx; id = n } else assert false }

atom :
| s = UVAR UNDERSCORE idx = ivar            { mk_uvar s ~idx:(Some idx) }
| s = UVAR                                  { mk_uvar s }

oexp_atom:
| a = atom;                            { [(NoInv,a)] };
| a = atom; EXP; n = INT               { repeat_element ((if n < 0 then Inv else NoInv),a) (abs n) }
| a = atom; EXP; LPAR; n = INT; RPAR   { repeat_element ((if n < 0 then Inv else NoInv),a) (abs n) }

monom:
| atoms=separated_list(STAR,oexp_atom) { mk_monom (L.concat atoms) };

monom_or_one:
| i = INT  { if i <> 1 then failwith "only 1 accepted here" else mk_monom [] }
| m = monom { m }

summand:
| m = monom    { Mon(m) };

sum:
| LPAR; SUM; ids=separated_list(COMMA,ID); COLON; m = summand; RPAR
   { mk_sum (L.map ~f:(fun s -> ({ name = s; id = 0}, Ivar.Set.empty)) ids ) m };

poly :
| n = INT                    { SP.of_const (BI.of_int n) }
| a = atom                   { SP.of_atom a }
| a = atom; EXP; n = INT
  { mk_poly [(BI.one, mk_sum [] (Mon(mk_monom (repeat_element ((if n < 0 then Inv else NoInv),a) (abs n)))))] }
| s = sum                    { mk_poly [(BI.one, s)] }
| f = poly; PLUS; g = poly   { SP.( f +! g) }
| f = poly; STAR; g = poly   { SP.( f *! g) }
| f = poly; MINUS; g = poly  { SP.( f -! g) }
| MINUS; f = poly            { SP.( zero -! f) }
| LPAR; f = poly; RPAR       { f };
| LPAR; f = poly; RPAR; EXP; e = INT { if e < 0
                                       then failwith "negative exponent only allowed for variables"
                                       else Wrules.power_poly f (BI.of_int e) }

qprefix :
| FORALL; ids = separated_list(COMMA,ID); COLON { L.map ~f:(fun s -> { name = s; id = 0}) ids };

is_eq :
| EQ   { Eq }
| INEQ  { InEq };

constr :
| qp = qprefix? f = poly sep = is_eq g = poly?
  { mk_constr (L.map (optional ~d:[] qp) ~f:(fun i -> (i, Ivar.Set.empty))) sep SP.(f -! (optional ~d:zero g)) };

param_type :
| s = GROUP { GroupName(s) }
| FIELD { Fp }
;

samp_vars :
| SAMP; vs = separated_nonempty_list(COMMA,UVAR)
  { L.map vs ~f:mk_uvar }
;

samp_vars_orcl :
| SAMP; vs = separated_nonempty_list(COMMA,UVAR); SEMICOLON
  { L.map vs ~f:mk_uvar }
;

typed_var :
| v = UVAR; COLON; ty = param_type;
  { match ty with | Fp -> (mk_param v, ty) | _ -> (mk_uvar v,ty) }
;

polys_group:
| LBRACK; ps = separated_list(COMMA,poly); RBRACK; IN; g = GROUP
{ List.map (fun p -> (p,g)) ps}

cmd :
| GROUPSETTING i = INT; DOT
  { GroupSetting(match i with 1 -> I | 2 -> II | 3 -> III | _ -> failwith "invalid group setting") }
| vs = samp_vars; DOT
  { AddSamplings(vs) }
| INP; LBRACK; ps = separated_nonempty_list(COMMA,poly); RBRACK; IN; g = GROUP; DOT
  { AddInput(ps,g) }
| ORACLE; oname = ONAME; LPAR; params = separated_list(COMMA,typed_var); RPAR;
  EQ; ouvar = list(samp_vars_orcl);
  RETURN; ps = separated_list(COMMA,polys_group); DOT
  { AddOracle(oname,params,List.concat ouvar,List.concat ps) }
| WIN; LPAR; params = separated_list(COMMA,typed_var); RPAR;
  EQ;  LPAR; conds  = separated_list(LAND,constr); RPAR; DOT;
  { SetWinning(params, mk_conj [] conds) }
;

cmds_t : cs = list(cmd); EOF; { cs };

instr :
| GOTO; n = INT; DOT;
  { GoTo(n) }
| COEFF; LPAR; uM = monom_or_one; RPAR; n = INT; DOT;
  { IntrCoeff(mon2umon uM, n) }
| SIMPLIFY; DOT;
  { Simplify }
| CASE_DIST; a = atom; DOT;
  { CaseDistinction(a) }
| CONTRADICTION; DOT;
  { Contradiction }
| UNIFORM; DOT;
  { Uniform }
| DIVIDE_PARAM; a = atom; DOT;
  { DivideByParam(a) }
| UNIFORM_VARS; DOT;
  { UniformVars }
| ASSURE_LAURENT; DOT;
  { AssureLaurent }
| CLEAR_INDP_EQS; DOT;
  { ClearIndpEqs }
| SPLIT_IN_FACTORS; a = INT; DOT;
  { SplitInFactors(a) }
| SIMPLIFY_COEFFS; DOT;
  { SimplifyCoeffs }

instrs_t : instrs = list(instr); EOF; { instrs };
