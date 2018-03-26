/**
   After the bison lexical parsing, check types of formulas and resolve names.

   Proving formulas is also semantic checking, rename this file, maybe name resolve or type check ?
*/

#include <string.h>
#include <stdio.h>
#include "folAST.h"
#include <stdlib.h>

short semantic_check_operator_definition(formula* op,
					 const struct folAST* ast,
					 const struct string_list* variables,
					 const struct formula_list* proofLocalDecl)
{
  // A valid declaration is for example :
  // extensionality == \A a : \A b : (\A x : x \in a <=> x \in b) => a = b

  // By prior syntax check, op->name != 0 and op->builtInOp == lnone
  short success = resolve_names(/*out*/op->definingFormula,
				ast->constants,
				ast->operators,
				variables,
				op->operands,
				proofLocalDecl);
  return success;

  // TODO Check that op->freeVariables are not quantified in the right-hand side formula
}

short semantic_check_reason(struct reason* r,
			    proof* p,
			    const struct folAST* ast)
{
  if (!r->formula)
    return 1; // ok, nothing to check

  if (r->formula->name) // propositional tautology
    {
      return resolve_names(r->formula, ast->constants,
			   ast->operators, p->variables,
			   0, p->operators);
    }
  else // forall instantiation
    {
      struct formula_list* subs = r->formula->operands;
      while (subs)
	{
	  if (!resolve_names(subs->formula_elem, ast->constants,
			     ast->operators, p->variables,
			     0, p->operators))
	    return 0;
	  subs = subs->next;
	}
    }

  return 1;
}

short semantic_error_in_proof_statement(const struct JustifiedFormula* jf,
					const struct folAST* ast,
					proof* p)
{
  if (jf->reason)
    {
      if (!resolve_names(jf->formula, ast->constants,
			 ast->operators, p->variables,
			 0, p->operators)
	  || !semantic_check_reason(jf->reason, p, ast))
	return 1;
    }
  else
    {
      // register this local operator
      if (!semantic_check_operator_definition(jf->formula,
					      ast,
					      p->variables, p->operators))
	return 1;
      p->operators = make_formula_list(jf->formula, p->operators);
    }

  return 0; // means statement jf is correct
}

short semantic_check_proof(proof* p, struct folAST* ast)
{
  if (p->formulaToProve->file && strcmp(p->formulaToProve->file, ast->file) != 0)
    return 1; // proof coming from EXTENDS statement, was already checked in its own module

  // Check p's formula to prove
  if (!resolve_names(p->formulaToProve, ast->constants,
		     ast->operators, p->variables,
		     0, p->operators))
    {
      // finish the error message
      printf(" in formula ");
      print_formula(p->formulaToProve);
      return 0;
    }

  // Then check each statement of proof p
  struct FormulaDList* t = p->cumulativeTruths;
  while (t)
    {
      if (semantic_error_in_proof_statement(t->jf, ast, p))
	break;
      struct FormulaDList* const u = t->next;
      if (!t->jf->reason)
	{
	  // Remove the list node, because it was registered in p->operators
	  remove_list_node(t);
	  free(t->jf);
	  free(t);
	}
      t = u;
    }
  if (t)
    {
      // finish the error message
      printf(" in formula ");
      print_formula(t->jf->formula);
    }

  if (p->goal == axiomScheme && !t)
    {
      ast->axiomSchemes = make_proof_list(p, ast->axiomSchemes);
    }
  return !t;
}

short semantic_check(struct folAST* ast)
{
  // First check ast's operator definitions
  short opDefsOk = 1;
  void all_ops_ok(const void* nodep, VISIT value, int level)
  {
    if (value == preorder || value == postorder)
      return;

    formula* op = *(formula**)nodep;

    if (op->file && strcmp(op->file, ast->file) != 0)
      return; // operator coming from EXTENDS statement, was already checked in its own module

    const struct formula_list* proofLocalDecl = 0; // not inside a proof
    opDefsOk &= semantic_check_operator_definition(op,
						   ast,
						   (struct string_list*)0,
						   proofLocalDecl);
  }

  twalk(ast->operators, all_ops_ok);
  if (!opDefsOk)
    return 0;

  // Then check ast's proofs
  short proofsOk = 1;
  void all_proofs_ok(const void* nodep, VISIT value, int level)
  {
    if (value == preorder || value == postorder)
      return;

    proof* p = *(proof**)nodep;
    proofsOk &= semantic_check_proof(p, ast);
  }
  twalk(ast->proofs, all_proofs_ok);

  if (!proofsOk)
    printf("Semantic error in proof\n");

  // TODO use axioms to type primitive operators (relations or operations).
  // If a primitive operator s has no axiom or cannot be typed, refuse it
  // and ask for an additional axiom
  // \A x : s(x) = s(x)   or   \A x : s(x) <=> s(x)

  return proofsOk;
}
