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
%token TO

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
%token EMAPS
%token ISOS

%token STAR
%token PLUS
%token MINUS
%token EXP

%token <string> GROUP
%token FIELD

%token <int> INT
%token <string> ID
		       
%token <string> RVAR
%token <string> ONAME


%token EXTRACT
%token CASE_DIST
%token GOTO
%token ADMIT
%token CONTRADICTION
%token UNIFORM
%token SIMPLIFY
%token SIMPLIFYVARS
       
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
| idx = ID                    { if (String.compare idx "k" <> 0) then { name = idx; id = 0 }
			        else failwith "index 'k' is reserved" }
| idx = ID; QUOTE;            { { name = idx; id = 1 } }
| idx = ID; QUOTE; n = INT    { if n > 0 then { name = idx; id = n } else assert false }
	
atom :
| s = RVAR UNDERSCORE idx = ivar            { mk_rvar s ~idx:(Some idx) }
| s = RVAR                                  { mk_rvar s }

oexp_atom:				
| a = atom;                            { [(NoInv,a)] };
| a = atom; EXP; n = INT               { repeat_element ((if n < 0 then Inv else NoInv),a) (abs n) }
| a = atom; EXP; LPAR; n = INT; RPAR   { repeat_element ((if n < 0 then Inv else NoInv),a) (abs n) }

monom:				
| atoms=separated_list(STAR,oexp_atom) { mk_monom (L.concat atoms) };

sum:
| LPAR; SUM; ids=separated_list(COMMA,ID); COLON; m = monom; RPAR
   { mk_sum (L.map ~f:(fun s -> { name = s; id = 0}) ids ) [] m };
    
poly :
| n = INT                    { SP.of_const (BI.of_int n) }
| a = atom                   { SP.of_a a }
| a = atom; EXP; n = INT
  { mk_poly [(BI.one, mk_sum [] [] (mk_monom (repeat_element ((if n < 0 then Inv else NoInv),a) (abs n))))] }
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
  { mk_constr (optional ~d:[] qp) [] sep SP.(f -! (optional ~d:zero g)) };

param_type :
| s = GROUP { s }
| FIELD { "Fp" }
;

samp_vars :
| SAMP; vs = separated_nonempty_list(COMMA,RVAR)
  { L.map vs ~f:mk_rvar }
;

samp_vars_orcl :
| SAMP; vs = separated_nonempty_list(COMMA,RVAR); SEMICOLON
  { L.map vs ~f:mk_rvar }
;

typed_var :
| v = RVAR; COLON; ty = param_type;
  { (mk_rvar v,ty) } 
;

polys_group:
| LBRACK; ps = separated_list(COMMA,poly); RBRACK; IN; g = GROUP
{ List.map (fun p -> (p,g)) ps}

emap :
| dom = separated_nonempty_list(STAR,GROUP); TO; _codom = GROUP
  { match dom with
    | g1 :: g2 :: [] -> (g1,g2)
    | _ -> failwith "emap: only bilinear maps supported" }
;

iso :
| dom = GROUP; TO; codom = GROUP { (dom,codom) }
;

cmd :
| EMAPS; emaps = separated_nonempty_list(COMMA,emap); DOT
  { AddMaps emaps }
| ISOS; isos = separated_nonempty_list(COMMA,iso); DOT
  { AddIsos isos }
| vs = samp_vars; DOT
  { AddSamplings(vs) }
| INP; LBRACK; ps = separated_nonempty_list(COMMA,poly); RBRACK; IN; g = GROUP; DOT
  { AddInput(ps,g) }
| ORACLE; oname = ONAME; LPAR; params = separated_list(COMMA,typed_var); RPAR;
  EQ; orvar = list(samp_vars_orcl);
  RETURN; ps = separated_list(COMMA,polys_group); DOT
  { AddOracle(oname,params,List.concat orvar,List.concat ps) }
| WIN; LPAR; params = separated_list(COMMA,typed_var); RPAR;
  EQ;  LPAR; conds  = separated_list(LAND,constr); RPAR; DOT;
  { SetWinning(params,conds) }
;

cmds_t : cs = list(cmd); EOF; { cs };

instr :
| EXTRACT; LPAR; idxs = separated_list(COMMA,ivar); SEMICOLON; m = monom; RPAR; n = INT; DOT;
  { Extract((idxs,m),n) }
| CASE_DIST; a = atom; DOT;
  { CaseDistinction(a) }
| GOTO; n = INT; DOT;
  { GoTo(n) }
| ADMIT; DOT;
  { Admit }
| CONTRADICTION; DOT;
  { Admit }
| UNIFORM; DOT;
  { Uniform }
| SIMPLIFY; DOT;
  { Simplify }
| SIMPLIFYVARS; DOT;
  { SimplifyVars }

instrs_t : instrs = list(instr); EOF; { instrs };

	   
