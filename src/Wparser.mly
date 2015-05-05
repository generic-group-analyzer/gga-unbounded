%{
  open Wconstrs
  open Watom
  open Util
  open Abbrevs
%}

%token EOF
%token <int> INT
%token <string> ID
%token FORALL
%token COMMA
%token COLON

/************************************************************************/
/* Production types */

%type <Wconstrs.constr> constr

/************************************************************************/
/* Start productions */
%start constr

%%

/************************************************************************/
/* Types */


qprefix :
| FORALL ids=separated_list(COMMA,ID) COLON { L.map ~f:(fun s -> { name = s; id = 0}) ids }

constr :
| qp=qprefix? n=INT EOF
  { mk_constr (Core.Std.Option.value ~default:[] qp) Eq (SP.of_const (BI.of_int n)) }
