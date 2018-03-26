#include "formula.h"

struct reason
{
  enum reason_kind rk;
  formula* formula; // can be a propositional tautology, or its operands can serve as forall substitutions
};
struct reason* make_reason(enum reason_kind k, formula* f);
void reason_free(struct reason* r);

struct JustifiedFormula
{
  formula* formula;
  struct reason* reason;
};
struct JustifiedFormula* make_jf(formula* f, struct reason* r);
void justified_formula_free(struct JustifiedFormula* jf);


/**
   To check a proof we need to go both forward and backward : read formulas forwards
   and check their reasons backwards.
*/
struct FormulaDList
{
  struct JustifiedFormula* jf;
  struct FormulaDList* next;
  struct FormulaDList* previous;
};
struct FormulaDList* push_justified_formula(struct JustifiedFormula* f, struct FormulaDList* next);
void f_list_free(struct FormulaDList* l);
void remove_list_node(struct FormulaDList* l);

struct proofS
{
  enum reason_kind goal; // axiom, theorem or complete_functional
  formula* formulaToProve;

  /**
     Variables that can have free occurrences in the formulas of the proof.
     This allows to distinguish from named operators.

     Or, for axiom schemes, variables that must be bound in the formula
     given to the scheme.
   */
  struct string_list* variables;
  struct formula_list* operators; // known only inside the proof
  struct FormulaDList* cumulativeTruths; // null for axioms
};
typedef struct proofS proof;

declare_list_type(proof)
declare_set_type(proof)

proof* make_proof(enum reason_kind proofGoal,
		  formula* formulaToProve,
		  struct string_list* variables,
		  struct FormulaDList* proof);
void proof_free(proof* p);
int compare_proofs(const void *l, const void *r);
short check_proof(const proof* proof, void* operators, void* assumedProofs,
				  const struct proof_list* axiomSchemes);
const struct FormulaDList* find_formula(const struct FormulaDList* formulas,
										short (*pred)(const struct JustifiedFormula* jf));
