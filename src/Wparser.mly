%{
  open Wconstrs
  open Util
%}

%token EOF
%token <int> INT

/************************************************************************/
/* Production types */

%type <Wconstrs.constr> constr

/************************************************************************/
/* Start productions */
%start constr

%%

/************************************************************************/
/* Types */

constr :
| n=INT EOF
  { mk_constr [] Eq (SP.of_const (BI.of_int n)) }
