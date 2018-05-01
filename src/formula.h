#include "list.h"

/**
   Operators composing formulas. Built-in means those operators
   are identified by a number (enum) instead of a name (char *),
   for faster comparison.

   Some of them can be defined in FOL files, like
   x \subseteq y == \A z : z \in x => z \in y

   They are also the only operators that can be postfix, infix
   or prefix without parenthesis.
*/
enum builtin_operator
  {
    // Not built-in means the operator is identified by a name (char *)
    lnone,

    // propositional (boolean) connectors
    lnot, lor, land, limplies, lequiv,

    // quantifiers
    forall, exists, choose, chooseUnique,

    // equality
    equal, different,

    // set relations
    in, notin, subset, subseteq,

    // set operations
    setEnumerate, // definition of a set by its elements, like {2, 8, 13}
    setSeparation,
    tuple,
    funcApply,
    binIntersect, binUnion, unaryUnion, powerset,

    plus, setDifference, cartesianProduct,

    // This type is set by the semantic checker, after the bison parsing.
    // A variable is either declared by
    //   - a quantifier (\A x : F)
    //   - a left-hand side variable list (x \subseteq y == ...)
    //   - the VARIABLES header of a proof. Without this header, a proof
    //     statement such as "zero \in one" could either be a universal
    //     quantification of zero and one, or refering to predeclared
    //     terms zero and one.
    variable,

    // used in the replacement axiom scheme
    schemeVariable
  };

const char* op_to_string(enum builtin_operator op);

/**
   Last part of a proof's statement
*/
enum reason_kind
  {
    propoTautology,
    modusPonens,
    generalization,
    theorem,
    axiom,
    axiomScheme,
    quantifierScheme,
    equalityScheme,
    forallInstance,
    existInstance,
    reasonChoose
  };
const char* reason_kind_to_string(enum reason_kind rk);

/**
   Storage struct for both propositional and first-order formulas. The bison parser
   garantees formulas are syntactically, however its LALR grammar cannot check formula's senses.
   For example bison accepts "x \lor y", with x and y being sets.

   semantic_check_fo_formula must be called after the bison parsing to finally accept or reject
   a formula.
*/
typedef struct formulaS
{
  enum builtin_operator builtInOp;

  /**
     An operator declaration like
     x \subseteq y == \A z : z \in x => z \in y
     parses as a formula with
     name = \subseteq, operands = x,y,
     defining formula = "\A z : z \in x => z \in y",

     A formula a \subseteq b parses as
     name = \subseteq, operands = "a,b", defining formula = 0

     builtInOp is a variable or quantifier, op->name is hacked to store the variable's name.
     op is a pointer, so that all formulas using custom operators point to the same definition.
  */
  char* name;

  struct formula_list* operands;


  /**
     See comment of name.

     When a formula f->builtInOp is a custom relation,
     f can often be replaced by the substitution
     f->definingFormula(x1 <- f->operand1, ..., xN <- f->operandN)
     
     The proof of the equivalence is as follows :
     f->builtInOp(x1, ..., xN) <=> f->definingFormula   BECAUSE AXIOM;
     \A x1 : ... \A xN : f->builtInOp(x1, ..., xN) <=> f->definingFormula   BECAUSE GENERALIZATION;
     f <=> f->definingFormula(x1 <- f->operand1, ..., xN <- f->operandN)   BECAUSE \A(x1 <- f->operand1, ...);

     which requires that all substitutions xK <- f->operandK are free in
     f->definingFormula. So for x \subseteq y == \A z : z \in x => z \in y,
     z \subseteq y is not equivalent to \A z : z \in z => z \in y.

     Also used for nullary operators and closed formulas (like axioms,
     theorems or the empty set), for quicker lookup.

     A formula is compared
     multiple times for modus ponens checking, resolve aliases only once.
     Shared by a lot of formulas, formula_free does not free it.
  */
  struct formulaS* definingFormula;


  /**
     Where the formula is defined (its == statement).
     Modules export their operator definitions but not their proofs.
     formula does not delete file, which is owned by its folAST.

     Used to verify that a BECAUSE THEOREM refers to a proof that is
     before in the file. The line is shown in error messages for easier
     corrections of proofs.
  */
  const char* file;
  long first_line;
} formula;
formula* make_formula(enum builtin_operator builtInOp,
		      const char* name, // takes ownership
		      struct formula_list* operands,
		      const char* file,
		      long first_line);
void formula_free(formula* f);
declare_list_type(formula)
declare_set_type(formula)
const formula* find_formula_same_name(const struct formula_list* l,
				      const formula* op);

typedef struct
{
  const char* variable;
  const formula* subst;
} variable_substitution;

declare_list_type(variable_substitution)
struct formula_list* clone_operands(const struct formula_list* operands,
				    variable_substitution* freeSubs);


int formula_compare_operators(const void *l, const void *r);
short operator_equal(const formula* f, const formula* g);
void print_formula(const formula* f);
short is_propositional_formula(const formula* f);
unsigned char prove_propositional_tautology(const formula* op);
const formula* get_first_operand(const formula* f);
const formula* get_second_operand(const formula* f);

/**
   Find a variable v of formula f satisfying predicate pred, which is given
   - the variable v
   - the union of boundVars and all the bound variables of f at v.
   - the same args as passed to find_variable
*/
const char* find_variable(const formula* f,
			  const struct string_list* boundVars,
			  unsigned char (*pred)(const char* v,
						const struct string_list* boundVars,
						const void* args),
			  const void* args);

/**
   Test both that freeSubs are valid for g and that f equals g(freeSubs).
   A valid free substitution a <- b in g means that, for all free occurrences
   of variable "a" in g, when substituted by b, all free occurrences of
   variables in "b" remain free in g.

   The substitutions are not ordered and applied all at once,
   so (x<-y, y<-z) is the same as (y<-z, x<-y).

   boundVariables restrict which variables are considered free.

   formula_equal only uses operators' defining formulas when they
   have no arguments (simple closed formulas aliases). In this case there
   is no risk to capture a variable.

   Boolean substituteMore allows to increase freeSubs, so that, when returning true,
   formula_equal(f, g, boundVariables, moreFreeSubs, false) is true.
*/
unsigned char formula_equal(const formula* f,
			    const formula* g,
			    const struct string_list* boundVariables,
			    variable_substitution* freeSubs,
			    unsigned char substituteMore);

variable_substitution* variable_substitution_find(const char* var,
												  variable_substitution* subst);
formula* formula_clone(const formula* f, variable_substitution* freeSubs);

short is_bound_variable(const formula* f, const char* v);
short is_custom_operator(const formula* op);

unsigned char resolve_names(formula* f,
			    const struct formula_list* primitives,
			    const formula_set operatorDefinitions,
			    const struct string_list* variables,
			    const struct formula_list* opVariables, // should be a union with variables
			    const struct formula_list* proofLocalDecl);

/**
   Checks whether f is a valid forall instance axiom, ie if there exists
   a formula F and a variable x such that f equals
   (\A x : F) => F(x <- t)
   where t is the term held in substitutions.

   The substitution x<-t must not capture variables : from the true formula
   "\A x : \E y : y # x", we cannot conclude the false formula
   "\E y : y # y".

   This function uses defining formulas of custom operators, which
   strictly tests that f equals G => F(x <- t), where G is equivalent to \A x : F.
   The complete proof would be
   G => (\A x : F)   BECAUSE DEFINING_FORMULAS;
   (\A x : F) => F(x <- t)   BECAUSE \A(x <- t);
   f   BECAUSE TransitImplication;   

   When applying several variable substitutions at once, this function
   considers the substitutions are unordered and not cumulative.
   For example, on variable a, the application of a <- b, b <- c yields b.
   Cumulative forall instantiations must be fully written on separate lines in proofs.
  
   In first-order logic, the forall instance axiom handles only one substitution,
   the multiple unordered case is derived by first renaming the quantified variables :
   (\A x1 : ... \A xN : F(x1, ..., xN))
      => \A x2 : ... \A xN : F(x1 <- xUnused1, x2, ... xN)   BECAUSE \A(x1 <- xUnused1);
   (\A x1 : ... \A xN : F(x1, ..., xN)) => F(x1 <- xUnused1, ..., xN <- xUnusedN)   BECAUSE TransitImplication;
   (\A x1 : ... \A xN : F(x1, ..., xN))
      => \A xUnused1 : ... \A xUnusedN : F(x1 <- xUnused1, ..., xN <- xUnusedN)   BECAUSE GENERALIZATION;
   then instantiate the unused variables cumulatively, they avoid name collisions.

   For example, the following statement is valid :
   (\A x : \A y : x # y) => y # x   BECAUSE \A(x <- y, y <- x);
   its strict first-order logic proof would be :
   (\A x : \A y : x # y) => (\A xUnused : \A yUnused : xUnused # yUnused)   BECAUSE RENAMING;
   (\A xUnused : \A yUnused : xUnused # yUnused) => (\A yUnused : y # yUnused)   BECAUSE \A(xUnused <- y);
   (\A yUnused : y # yUnused) => y # x   BECAUSE \A(yUnused <- x);
   (\A xUnused : \A yUnused : xUnused # yUnused) => y # x   BECAUSE TransitImplication;
   (\A x : \A y : x # y) => y # x   BECAUSE TransitImplication;

   This function is called in a loop on jf's previous formulas,
   do not write error messages in it.

   Also handle the symmetric case, exist instance :
   f(x <- t) => \E x : f when t is free for x.
  
   which could be deduced as
   (\A x : ~f) => ~f(x <- t)   BECAUSE \A(x <- t) (t is free for x)
   f(x <- t) => \E x : f   BECAUSE Contraposition
*/
short check_quantifier_instance_statement_one(enum reason_kind rk,
					      const formula* f,
					      struct formula_list* substitutions, // TODO variable_substitution_set
					      const formula_set ops);

/**
   Assume propoTaut is a propositional formula (only logical operators) and
   search substitutions for the propositional variables that yield formula f.

   The substitutions are not cumulative : the propositional variables are replaced
   by first-order formulas, which are no longer propositional.

   In the strict first-order logic axioms, only 14 propositional tautologies
   are taken as axioms, the others being deduced from them by modus ponens.
   But a first-order instance of any propositional tautology is true
   in all models, because a tautology is true for any values of its
   propositional variables. By Gödel's completeness theorem such
   instances are provable, so we take them all as axioms.
*/
short check_propositional_tautology_statement_one(const formula* f,
						  const formula* propoTaut,
						  const formula_set ops);
