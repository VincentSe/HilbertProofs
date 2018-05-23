%{
#include "folAST.h"
#include "fol.tab.h"
#define YYSTYPE         FOLSTYPE
#define YYLTYPE         FOLLTYPE
#define YY_USER_ACTION yylloc->first_line = yylloc->last_line = yylineno;
void folerror (YYLTYPE* yylloc, void* scanner, struct folAST* ast, char const* errorMsg);
%}

%option noyywrap
%option reentrant bison-bridge
%option bison-locations
%option never-interactive
%option nounistd

%x FOL_COMMENT

%%

[ \t]+        { /* ignore */ }
"~"           { folget_lval(yyscanner)->lopVal = lnot; return LNOT; }
"\\/"         { folget_lval(yyscanner)->lopVal = lor; return LOGICAL_ANDOR_OP; }
"/\\"         { folget_lval(yyscanner)->lopVal = land; return LOGICAL_ANDOR_OP; }
"=>"          { folget_lval(yyscanner)->lopVal = limplies; return LOGICAL_BIN_OP; }
"<=>"         { folget_lval(yyscanner)->lopVal = lequiv; return LOGICAL_BIN_OP; }

"UNION"       { folget_lval(yyscanner)->lopVal = unaryUnion; return PREFIX_OP; }
"SUBSET"      { folget_lval(yyscanner)->lopVal = powerset; return PREFIX_OP; }
"\\in"        { folget_lval(yyscanner)->lopVal = in; return INFIX_REL; }
"\\notin"     { folget_lval(yyscanner)->lopVal = notin; return INFIX_REL; }
"="           { folget_lval(yyscanner)->lopVal = equal; return INFIX_REL; }
"#"           { folget_lval(yyscanner)->lopVal = different; return INFIX_REL; }
"\\subseteq"  { folget_lval(yyscanner)->lopVal = subseteq; return INFIX_REL; }
"\\intersect" { folget_lval(yyscanner)->lopVal = binIntersect; return INFIX_OP; }
"\\union"     { folget_lval(yyscanner)->lopVal = binUnion; return INFIX_OP; }
"\\X"         { folget_lval(yyscanner)->lopVal = cartesianProduct; return INFIX_OP; }
"+"           { folget_lval(yyscanner)->lopVal = plus; return INFIX_OP; }
"\\"          { folget_lval(yyscanner)->lopVal = setDifference; return INFIX_OP; }


"\\A"     { folget_lval(yyscanner)->lopVal = forall; return QUANTIFIER; }
"\\E"     { folget_lval(yyscanner)->lopVal = exists; return QUANTIFIER; }


"AXIOM"          { folget_lval(yyscanner)->rkVal = axiom; return REASON_KIND; }
"AXIOM_SCHEME"   { folget_lval(yyscanner)->rkVal = axiomScheme; return REASON_KIND; }
"Q_SCHEME"       { folget_lval(yyscanner)->rkVal = quantifierScheme; return REASON_KIND; }
"E_SCHEME"       { folget_lval(yyscanner)->rkVal = equalityScheme; return REASON_KIND; }
"THEOREM"        { folget_lval(yyscanner)->rkVal = theorem; return REASON_KIND; }
"MACRO"          { folget_lval(yyscanner)->rkVal = macro; return REASON_KIND; }
"PROPO_TAUTO"    { folget_lval(yyscanner)->rkVal = propoTautology; return REASON_KIND; }
"MODUS_PONENS"   { folget_lval(yyscanner)->rkVal = modusPonens; return REASON_KIND; }
"GENERALIZATION" { folget_lval(yyscanner)->rkVal = generalization; return REASON_KIND; }

"BOUND_VAR" { return BOUND_VAR; }
"<-" { return LEFT_ARROW; }

\\\*[^\n]*$ { /* discard line comments */ }
\r { /* discard carriage returns */ }

"CHOOSE"  { return CHOOSE; }
"CHOOSE_UNIQUE"  { return CHOOSE_UNIQUE; }
"LOCAL" { return LOCAL; }
"PROOF" { return PROOF; }
"QED" { return QED; }
"BECAUSE" { return BECAUSE; }
"CONSTANT" { return CONSTANT; }
"EXTENDS" { return EXTENDS; }
"VARIABLES" { return VARIABLES; }
","  { return COMMA; }
";"  { return SEMICOLON; }
":"  { return COLON; }
"_" { return UNDERSCORE; }

[a-zA-Z0-9]+ {
  folget_lval(yyscanner)->sVal = strdup(yytext);
  return NAME; }

"=="  { return NAME_SEPARATOR; }
"("   { return LEFT_PARENTHESIS; }
")"   { return RIGHT_PARENTHESIS; }
"{"   { return LEFT_BRACE; }
"}"   { return RIGHT_BRACE; }
"["   { return LEFT_BRACKET; }
"]"   { return RIGHT_BRACKET; }
"<<"  { return LEFT_TUPLE; }
">>"  { return RIGHT_TUPLE; }
\n+   { yylineno += strlen(yytext); }

.     { folerror (yylloc, yyscanner, (struct folAST*)0, "unknown character"); }  // don't silently convert "y'" to "y" as a variable name for instance

"(*"              { BEGIN(FOL_COMMENT); }
<FOL_COMMENT>"*)" { BEGIN(INITIAL); }
<FOL_COMMENT>\n   { yylineno += 1; }
<FOL_COMMENT>.    { } // Discard block comments

%%
