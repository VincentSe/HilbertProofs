/**
   Header included by fol.y, to produce an abstract syntax tree
   of first-order formulas.
*/

#include <search.h>
#include "list.h"
#include "proof.h"

struct folAST // result of the bison parsing
{
  char* file; // the file parsed to produce this AST

  /**
     Tree of operators, sorted by names for fast lookup in proofs.
     merge_asts recursively includes operators from extended modules.
   */
  formula_set operators;

  /**
     Proofs are not ordered and almost independant from each other.
     When F BECAUSE THEOREM is invoked inside a proof P, it only checks
     that formula F
        - has a proof
	- is before P in the FOL file (to prevent cyclic proofs)
     However F BECAUSE THEOREM does not check that F's proof is correct.
   */
  proof_set proofs;
  
  struct proof_list* axiomSchemes; // those cannot be searched by name, all of them must be tried for substitution of a candidate axiom formula
  struct string_list* extends;
  struct formula_list* constants;
};
struct folAST* make_folAST(const char* file);
void folAST_free(struct folAST* ast);

short declare_operator(formula* op, /*out*/struct folAST* ast);
void add_proof(proof* p, /*out*/struct folAST* ast);
void add_extends(char* p, /*out*/struct folAST* ast);
void add_constants(struct formula_list* p, /*out*/struct folAST* ast);

formula* check_operator_definition(formula* left, formula* right);
int parse_fo_formulas(/*out*/struct folAST* ast);
short semantic_check(struct folAST* ast);
unsigned char resolve_extends(/*out*/struct folAST** asts, /*out*/unsigned int* astSort);
