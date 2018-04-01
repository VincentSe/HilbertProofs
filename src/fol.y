/* First-order logic and Hilbert-style proofs. */

%{
#include <stdio.h>
#include <string.h>
#include "folAST.h"
#include "fol.tab.h" // doesn't insert itself in itself, only in fol.tab.c
  void folerror (YYLTYPE* yylloc, void* scanner, struct folAST* ast, char const* errorMsg);
  int follex(YYSTYPE*, YYLTYPE*, void* scanner);
  %}

%union
 {
   char cVal;
   char* sVal;
   enum builtin_operator lopVal;
   enum reason_kind rkVal;
   formula* formulaVal;
   struct FormulaDList* jflVal;
   struct formula_list* flVal;
   struct string_list* slVal;
   struct JustifiedFormula* jVal;
   struct reason* rVal;
   proof* pVal;
}

%define api.prefix {fol}
%locations
%define api.pure full
%lex-param {void* scanner}
%parse-param {void* scanner} {struct folAST* ast}
%error-verbose
%defines

%token NAME_SEPARATOR
%token RIGHT_PARENTHESIS
%token LEFT_BRACE RIGHT_BRACE LEFT_BRACKET RIGHT_BRACKET LEFT_TUPLE RIGHT_TUPLE
%token <rkVal> REASON_KIND

%precedence <lopVal> QUANTIFIER
%left       <lopVal> LOGICAL_BIN_OP
%precedence <lopVal> LNOT
%left       <lopVal> INFIX_OP
%precedence <lopVal> PREFIX_OP

%precedence <sVal> NAME
%precedence LEFT_PARENTHESIS
%token PROOF QED COMMA SEMICOLON COLON BECAUSE CONSTANT UNDERSCORE VARIABLES EXTENDS BOUND_VAR LEFT_ARROW LOCAL

%type  <formulaVal> formula
%type  <formulaVal> setDef
%type  <formulaVal> tuple
%type  <formulaVal> operatorDefinition
%type  <formulaVal> constant
%type  <formulaVal> funcApply
%type  <jflVal> justifiedFormulas
%type  <jVal> justifiedFormula
%type  <rVal> reason
%type  <flVal> commaSeparatedFormulas
%type  <flVal> commaSeparatedSubstitutions
%type  <flVal> substitution
%type  <flVal> constants
%type  <slVal> schemeClause
%type  <pVal> proof
%type  <slVal> variables
%type  <slVal> proofHeader

%%

statements:
%empty {}
| operatorDefinition statements {
  if (!declare_operator($1, ast))
    yyerror(&@$, scanner, ast, "This first order formula's name is already used.\n"); }
| proof statements { add_proof($1, ast); }
| constants statements { add_constants($1, ast); }
| EXTENDS NAME statements { add_extends($2, ast); }
;

constants: constant { $$ = make_formula_list($1, 0); }
| constant COMMA constants { $$ = make_formula_list($1, $3); }
;

// Constants (primitive symbols) declare their arity but not their being relations or operators
constant:
CONSTANT UNDERSCORE INFIX_OP UNDERSCORE {
  $$ = make_formula($3,
		    (char*)0,
		    (struct formula_list*)0,
		    ast->file,
		    @1.first_line); }
| CONSTANT PREFIX_OP UNDERSCORE {
  $$ = make_formula($2,
		    (char*)0,
		    (struct formula_list*)0,
		    ast->file,
		    @1.first_line); }
;

variables:
NAME { $$ = make_string_list($1, 0); }
| variables COMMA NAME { $$ = make_string_list($3, $1); }
;

// All free variables in named formula declarations must also appear on the left-hand side,
// between parantheses after the name.
operatorDefinition:
formula NAME_SEPARATOR formula {
  $$ = check_operator_definition($1, $3);
  if (!$$)
    yyerror(&@$, scanner, ast, "Bad operator definition"); }
| LOCAL formula NAME_SEPARATOR formula {
  $$ = check_operator_definition($2, $4);
  if (!$$)
    yyerror(&@$, scanner, ast, "Bad operator definition"); }
| formula NAME_SEPARATOR formula SEMICOLON { // local operators in proofs
  $$ = check_operator_definition($1, $3);
  if (!$$)
    yyerror(&@$, scanner, ast, "Bad operator definition"); }
;

proofHeader:
PROOF  { $$ = (struct string_list*)0; }
| PROOF VARIABLES variables SEMICOLON { $$ = $3; }
;

proof:
REASON_KIND formula proofHeader justifiedFormulas QED {
  $$ = make_proof($1, $2, $3, $4); }
| REASON_KIND formula { // axioms and propositional tautologies have no written proofs
  $$ = make_proof($1, $2, 0, 0); }
| REASON_KIND schemeClause formula {
  $$ = make_proof($1, $3, $2, 0); }
;

schemeClause: BOUND_VAR LEFT_PARENTHESIS variables RIGHT_PARENTHESIS {
  $$ = $3; }
;

commaSeparatedFormulas:
formula { $$ = make_formula_list($1, (struct formula_list*)0); }
| formula COMMA commaSeparatedFormulas { $$ = make_formula_list($1, $3); }
;

commaSeparatedSubstitutions:
substitution { $$ = $1; }
| substitution COMMA commaSeparatedSubstitutions {
  $$ = make_formula_list($1->formula_elem,
			 make_formula_list($1->next->formula_elem, $3));
  $1->formula_elem = 0;
  $1->next->formula_elem = 0;
  formula_list_free($1); }
;

substitution : NAME LEFT_ARROW formula {
  // Drop the arrow and convert it to a pair (name, formula)
  formula* name = make_formula(lnone,
			       $1,
			       (struct formula_list*)0,
			       ast->file,
			       @1.first_line);
  $$ = make_formula_list(name, make_formula_list($3, (struct formula_list*)0)); }
;

// bison's LALR parser cannot parse a grammar that distinguishes terms and formulas. Check after the parsing. No infix functions, only infix operators taken from a limited list of keywords
formula:
NAME { // operator or variable as a leaf of this formula
  $$ = make_formula(lnone,
		    $1,
		    (struct formula_list*)0,
		    ast->file,
		    @1.first_line); }
| NAME LEFT_PARENTHESIS commaSeparatedFormulas RIGHT_PARENTHESIS {
  $$ = make_formula(lnone,
		    $1,
		    $3,
		    ast->file,
		    @1.first_line); }
| NAME LEFT_PARENTHESIS commaSeparatedSubstitutions RIGHT_PARENTHESIS {
  $$ = make_formula(schemeVariable,
		    $1,
		    $3,
		    ast->file,
		    @1.first_line); }
| LEFT_PARENTHESIS formula RIGHT_PARENTHESIS {  $$ = $2; }
| QUANTIFIER NAME COLON formula %prec QUANTIFIER {
  $$ = make_formula($1,
		    $2,
		    make_formula_list($4, 0),
		    ast->file,
		    @1.first_line); }
| PREFIX_OP formula {
  $$ = make_formula($1,
		    (char *)0,
		    make_formula_list($2, 0),
		    ast->file,
		    @1.first_line); }
| formula INFIX_OP formula {
  $$ = make_formula($2,
		    (char *)0,
		    make_formula_list($1, make_formula_list($3, 0)),
		    ast->file,
		    @1.first_line); }
| formula LOGICAL_BIN_OP formula {
  // logical bin ops cannot be redefined, leave them without name
  $$ = make_formula($2,
		    (char*)0,
		    make_formula_list($1, make_formula_list($3, 0)),
		    ast->file,
		    @1.first_line); }
| LNOT formula {
  $$ = make_formula($1,
		    (char*)0,
		    make_formula_list($2, 0),
		    ast->file,
		    @1.first_line); }
| setDef | tuple | funcApply
;

funcApply: NAME LEFT_BRACKET formula RIGHT_BRACKET {
  formula* funcFormula = make_formula(lnone,
				      $1,
				      (struct formula_list*)0,
				      ast->file,
				      @1.first_line);
  $$ = make_formula(funcApply, (char*)0,
		    make_formula_list(funcFormula, make_formula_list($3, 0)),
		    ast->file,
		    @1.first_line);
}
;

justifiedFormula:
formula BECAUSE reason SEMICOLON { $$ = make_jf($1, $3); }
| operatorDefinition { // local formula definition inside a proof
  $$ = make_jf($1, (struct reason*)0); }
;

justifiedFormulas:
justifiedFormula { $$ = push_justified_formula($1, 0); }
| justifiedFormula justifiedFormulas { $$ = push_justified_formula($1, $2); }
;

reason:
NAME { $$ = make_reason(propoTautology,
			make_formula(lnone,
				     $1,
				     (struct formula_list*)0,
				     ast->file,
				     @1.first_line)); }
| REASON_KIND { $$ = make_reason($1, (formula*)0); }
| QUANTIFIER LEFT_PARENTHESIS commaSeparatedSubstitutions RIGHT_PARENTHESIS {
  if ($1 != forall && $1 != exists)
    yyerror(&@$, scanner, ast, "Substitutions in a reason must be \\A or \\E.\n");
  $$ = make_reason($1 == forall ? forallInstance : existInstance,
		   make_formula(lnone,
				(char*)0,
				$3,
				ast->file,
				@1.first_line)); }
| QUANTIFIER {
  if ($1 != choose)
    yyerror(&@$, scanner, ast, "A quantifier in a reason should be CHOOSE.\n");
  $$ = make_reason(reasonChoose, (formula*)0);
  }
;

setDef:
LEFT_BRACE commaSeparatedFormulas RIGHT_BRACE {
  $$ = make_formula(setEnumerate,
		    (char*)0,
		    $2,
		    ast->file,
		    @1.first_line); }
| LEFT_BRACE formula INFIX_OP formula COLON formula RIGHT_BRACE {
  $$ = make_formula(setSeparation,
		    strdup(op_to_string(setSeparation)),
		    make_formula_list($2, make_formula_list($4, make_formula_list($6, 0))),
		    ast->file,
		    @1.first_line); }
| LEFT_BRACE RIGHT_BRACE { // empty set
  $$ = make_formula(setEnumerate,
		    (char*)0,
		    (struct formula_list*)0,
		    ast->file,
		    @1.first_line); }
;

tuple:
LEFT_TUPLE commaSeparatedFormulas RIGHT_TUPLE {
  $$ = make_formula(tuple,
		    (char*)0,
		    $2,
		    ast->file,
		    @1.first_line); }
;
