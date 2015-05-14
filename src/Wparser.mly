%{
  open Wconstrs
  open Watom
  open Util
  open Abbrevs
%}

%token EOF
%token <int> INT
%token <string> ID
			       
%token <string> RVAR
%token <string> PARAM
%token <string> HVAR
			         
%token FORALL
%token SUM		       
%token COMMA
%token COLON
%token UNDERSCORE
%token AT

%token LPAR
%token RPAR

%token STAR
%token PLUS
%token MINUS
%token HAT

%token EQ
%token NEQ

/************************************************************************/       
/* Priority & associativity */

/* Multiplication has the highest precedence. */
%left PLUS MINUS
%left STAR       

/************************************************************************/
/* Production types */

%type <Watom.ivar> ivar      
%type <Wconstrs.constr> constr
%type <Wconstrs.monom> monom_read
%type <Wconstrs.poly> poly_read
					       
/************************************************************************/
/* Start productions */

%start ivar   
%start constr
%start monom_read
%start poly_read
       
%%

/************************************************************************/
/* Types */
 
ivar :
| idx = ID         { { name = idx; id = 0 } };
 
atom :
| s = RVAR UNDERSCORE idx = ivar            { mk_rvar s ~idx:(Some idx) }
| s = PARAM UNDERSCORE idx = ivar           { mk_param s ~idx:(Some idx) }
| s = HVAR UNDERSCORE idx = ivar AT g = INT
       { mk_hvar ~idx (match g with | 1 -> G1 | 2 -> G2 | _ -> failwith "Unknown group") s }
| s = RVAR                                  { mk_rvar s }
| s = PARAM                                 { mk_param s };

oexp_atom:				
| a = atom; HAT; n = INT               { repeat_element ((if n < 0 then Inv else NoInv),a) (abs n) }
| a = atom; HAT; LPAR; n = INT; RPAR   { repeat_element ((if n < 0 then Inv else NoInv),a) (abs n) }
| a = atom;                            { [(NoInv,a)] };

monom:				
| atoms=separated_list(STAR,oexp_atom) { mk_monom (L.concat atoms) };

sum:
| LPAR; SUM; ids=separated_list(COMMA,ID); COLON; m = monom; RPAR
   { mk_sum (L.map ~f:(fun s -> { name = s; id = 0}) ids ) [] m };
    
poly :
| n = INT                    { SP.of_const (BI.of_int n) }
| a = atom                   { SP.of_a a }
| s = sum                    { mk_poly [(BI.one, s)] }
| f = poly; PLUS; g = poly   { SP.( f +! g) }
| f = poly; STAR; g = poly   { SP.( f *! g) }
| f = poly; MINUS; g = poly  { SP.( f -! g) }
| MINUS; f = poly            { SP.( zero -! f) }
| LPAR;  f = poly; RPAR      { f };

  
qprefix :
| FORALL; ids = separated_list(COMMA,ID); COLON { L.map ~f:(fun s -> { name = s; id = 0}) ids };
  
is_eq :
| EQ   { Eq }
| NEQ  { InEq };
  
constr :
| qp = qprefix? f = poly sep = is_eq g = poly? EOF
  { mk_constr (optional ~d:[] qp) [] sep SP.(f -! (optional ~d:zero g)) };

monom_read:
| m = monom EOF   { m }

poly_read:
| p = poly EOF	  { p }   
