#include "folAST.h"
#include "fol.tab.h"
#define YYSTYPE         FOLSTYPE
#define YYLTYPE         FOLLTYPE
#include "lex.fol.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "graph.h"

void folerror(YYLTYPE* yylloc,
	      void* scanner,
	      struct folAST* ast,
	      char const* errorMsg)
{
  // function printing errors during flex and bison parsing
  printf("%s:%d: %s at %s\n",
	 ast ? ast->file : "",
	 yylloc->first_line,
	 errorMsg,
	 folget_text(scanner));
}

// Slightly more portable than the GNU version. Slower ?
void tdestroy (void* vrootp, void (*deleter)(void*))
{
  int fakeComparer(const void* x, const void* y) {
    deleter((void*)y);
    return 0; // take first element in the tree
  }
  while (tdelete(0, &vrootp, fakeComparer))
    ;
}

struct folAST* make_folAST(const char* file)
{
  struct folAST* ast = malloc(sizeof(struct folAST));
  ast->file = strdup(file);
  ast->extends = 0;
  ast->operators = 0;
  ast->operators_by_line = 0;
  ast->proofs = 0;
  ast->axiomSchemes = 0;
  ast->constants = 0;
}

void reverse_free(struct formula_list* l)
{
  if (!l)
    return;
  reverse_free(l->next);
  formula_free(l->formula_elem->definingFormula);
  l->formula_elem->definingFormula = 0;
  formula_free(l->formula_elem);
  free(l);
}

void folAST_free(struct folAST* ast)
{
  if (!ast) return;

  void proof_deleter(void* t)
  {
    proof* p = t;
    if (p->formulaToProve->file
	&& strcmp(p->formulaToProve->file, ast->file) == 0)
      proof_free(p);
  }
  tdestroy(ast->proofs, proof_deleter);
  reverse_free(ast->operators_by_line);
  
  void deleter(void* t)
  {
  }
  tdestroy(ast->operators, deleter); // destroy operator definitions last, because the proofs point to them
  free(ast->file);
  string_list_free(ast->extends);

  struct proof_list* schemes = ast->axiomSchemes;
  while (schemes)
    {
      schemes->proof_elem = 0; // the proofs own their conclusions
      schemes = schemes->next;
    }
  proof_list_free(ast->axiomSchemes);
  formula_list_free(ast->constants);

  free(ast);
}

void add_extends(char* ext, /*out*/struct folAST* ast)
{
  ast->extends = make_string_list(ext, ast->extends);
}

void add_constants(struct formula_list* p, /*out*/struct folAST* ast)
{
  ast->constants = p; // TODO concatenate lists
}

void add_proof(proof* p, /*out*/struct folAST* ast)
{
  if (!p)
    return;
  proof** tf = tsearch(p, &ast->proofs, compare_proofs);
  if (tf && p != *tf)
    {
      printf("%s:%d: Multiple proofs of %s\n",
	     p->formulaToProve->file,
	     p->formulaToProve->first_line,
	     p->formulaToProve->name);
      proof_free(p);
    }
}

int parse_fo_formulas(/*out*/struct folAST* ast)
{
  yyscan_t myscanner;
  follex_init(&myscanner);
  FILE* in = fopen(ast->file, "r");
  folset_in(in, myscanner);
  if (!in)
    {
      printf("Cannot find proof file %s.\n", ast->file);
      return 1;
    }

  const int success = folparse(myscanner, /*out*/ast);
  follex_destroy(myscanner);
  fclose(in);
  return success;
}

struct string_list* make_string_list(char* name, struct string_list* next)
{
  struct string_list* sl = malloc(sizeof(struct string_list));
  sl->string_elem = name;
  sl->next = next;
  return sl;
}

void string_list_free(struct string_list* l)
{
  if (!l) return;
  free(l->string_elem);
  string_list_free(l->next);
  free(l);
}

int string_list_size(const struct string_list* l)
{
  if (!l) return 0;
  return 1 + string_list_size(l->next);
}

short string_list_contains(const struct string_list* l, const char* string)
{
  if (string) while (l)
    {
      if (strcmp(l->string_elem, string) == 0)
	return 1;
      l = l->next;
    }
  return 0;
}

short declare_operator(formula* op, struct folAST* ast)
{
  if (op->builtInOp == lnone && !op->name)
    {
      printf("Declaring a formula without name\n");
      formula_free(op);
      return 0;
    }

  ast->operators_by_line = make_formula_list(op, ast->operators_by_line);

  formula** tf = tsearch(op, &ast->operators, formula_compare_operators);
  if (tf && op != *tf)
    {
      printf("%s:%d: Multiply defined operator : %s\n",
	     op->file,
	     op->first_line,
	     op->name);
      formula_free(op);
      return 0;
    }
  return 1;
}

short merge_asts(/*out*/struct folAST* ast,
		 const struct folAST* knownAst)
{
  void insert_operator(const void* nodep, VISIT value, int level)
  {
    if (value == preorder || value == postorder)
      return;

    formula* op = *(formula**)nodep;
    formula** tf = tsearch(op, &ast->operators,
				  formula_compare_operators);
    if (tf && op != *tf)
      {
	printf("%s:%d: Multiply defined operator : %s\n",
	       op->file,
	       op->first_line,
	       op->name);
	return;
      }
  }
  twalk(knownAst->operators, insert_operator);

  void insert_proof(const void* nodep, VISIT value, int level)
  {
    if (value == preorder || value == postorder)
      return;

    proof* p = *(proof**)nodep;
    proof** tf = tsearch(p, &ast->proofs, compare_proofs);
    if (tf && p != *tf)
      {
	printf("Multiply defined proof : %s", p->formulaToProve->name);
	return;
      }
  }
  twalk(knownAst->proofs, insert_proof);

  struct formula_list* prim = knownAst->constants;
  while (prim)
    {
      // TODO share formulas
      ast->constants = make_formula_list(formula_clone(prim->formula_elem, (variable_substitution*)0),
					 ast->constants);
      prim = prim->next;
    }

  struct proof_list* schemes = knownAst->axiomSchemes;
  while (schemes)
    {
      // folAST don't delete the proofs in axiomSchemes, sharing is OK
      ast->axiomSchemes = make_proof_list(schemes->proof_elem, ast->axiomSchemes);
      schemes = schemes->next;
    }
  return 1;
}

char *rindex(const char *s, int c)
{
  int l = strlen(s);
  const char* idx = s + l - 1;
  while (idx >= s)
    {
      if (*idx == c)
	return (char*)idx;
      idx--;
    }
  return 0;
}

unsigned int ast_idx(struct folAST ** asts, const char* name)
{
  unsigned int astIdx = 0;
  while (asts[astIdx])
    {
      const char* slash = rindex(asts[astIdx]->file, '/');
      if (strstr(slash, name))
	return astIdx;
      astIdx++;
    }
  return -1;
}

void default_sort(/*out*/struct folAST** asts,
		  /*out*/unsigned int* astSort)
{
  // The ASTs can be deleted in any order, put identity
  unsigned int i=0;
  while (asts[i])
    {
      astSort[i] = i;
      i++;
    }
}

unsigned char resolve_extends(/*out*/struct folAST** asts,
			      /*out*/unsigned int* astSort)
{
  // topological sort of asts
  arc extends[32];
  int extCount = 0;
  unsigned int astIdx = 0, i;
  while (asts[astIdx])
    {
      struct string_list* ext = asts[astIdx]->extends;
      while (ext)
	{
	  extends[extCount].first = ast_idx(asts, ext->string_elem);
	  if (extends[extCount].first == -1)
	    {
	      printf("%s:1: extends unknown module %s\n",
		     asts[astIdx]->file,
		     ext->string_elem);
	      default_sort(asts, /*out*/astSort);
	      return 0;
	    }
	  extends[extCount].second = astIdx;
	  extCount++;
	  ext = ext->next;
	}
      astIdx++;
    }

  if (!topological_sort(extends, extCount, astIdx, /*out*/astSort))
    {
      printf("Cycle in module extensions\n");
      default_sort(asts, /*out*/astSort);
      return 0;
    }

  // Type checking and proof checking of sorted asts
  struct folAST* ast = 0;
  void check_proof_closure(const void* nodep, VISIT value, int level)
  {
    if (value == preorder || value == postorder)
      return;
		
    proof* p = *(proof**)nodep;
    if (strcmp(ast->file, p->formulaToProve->file) == 0) // don't check proofs coming from other ASTs
      check_proof(p, ast->operators, ast->constants, ast->proofs, ast->axiomSchemes);
  }

  // semantic check of sorted asts
  for (i = 0; i < astIdx; i++)
    {
      ast = asts[astSort[i]];
      if (!semantic_check(ast))
	return 0;
      
      printf("Checking proofs of file %s:\n", ast->file);
      twalk(ast->proofs, check_proof_closure);

      // asts[sort[i]] is checked, merge it into all asts that extend it.
      for (int j = 0; j < extCount; j++)
	if (extends[j].first == astSort[i]
	    && !merge_asts(/*out*/asts[extends[j].second], ast))
	  return 0;
    }
  
  return 1;
}

void set_scheme_variables(const struct formula_list* variables,
			  /*out*/formula* f)
{
  if (f->builtInOp == variable
      && find_formula_same_name(variables, f))
    f->builtInOp = schemeVariable;

  struct formula_list* oper = f->operands;
  while (oper)
    {
      set_scheme_variables(variables, oper->formula_elem);
      oper = oper->next;
    }
}

unsigned char semantic_check_tautology(formula* tauto,
				       const formula_set operators)
{
  if (tauto->builtInOp != lnone || !tauto->name)
    {
      printf("%s:%d: propositional tautologies must be named\n",
	     tauto->file,
	     tauto->first_line);
      return 0;
    }

  formula* def = formula_set_find(tauto, operators);
  if (!def)
    {
      printf("%s:%d: unknown tautology %s\n",
	     tauto->file,
	     tauto->first_line,
	     tauto->name);
      return 0;
    }

  tauto->definingFormula = def->definingFormula;
  return 1;
}

/**
   A statement THEOREM F or PROPO_TAUTO F can be invoked multiple times
   in other proofs, as F BECAUSE THEOREM or BECAUSE F. Formula F is usually
   only the name of an operator, this function finds the corresponding
   defining formula and sets it in p->formulaToProve->definingFormula.
 */
short semantic_check_proof(proof* p, struct folAST* ast)
{
  if (p->formulaToProve->file
      && strcmp(p->formulaToProve->file, ast->file) != 0)
    return 1; // proof coming from EXTENDS statement, was already checked in its own module

  if (p->goal == macro)
    {
      for (const struct formula_list* op = p->formulaToProve->operands; op; op = op->next)
	{
	  if (op->formula_elem->builtInOp != lnone || op->formula_elem->operands)
	    {
	      printf("%s:%d: the operands of a macro must be variables %s\n",
		     p->formulaToProve->file,
		     p->formulaToProve->first_line);
	      return 0;
	    }
	  op->formula_elem->builtInOp = variable;
	}
      return 1; // macros are checked in other proofs, where they are copy-pasted
    }

  if (p->goal == propoTautology)
    return semantic_check_tautology(p->formulaToProve, ast->operators);

  if (p->goal == axiomScheme)
    {
      formula* resolvedF = formula_set_find(p->formulaToProve, ast->operators);
      if (!resolvedF)
	{
	  printf("%s:%d: unknown axiom scheme %s\n",
		 p->formulaToProve->file,
		 p->formulaToProve->first_line,
		 p->formulaToProve->name);
	  return 0;
	}
      p->formulaToProve->definingFormula = resolvedF->definingFormula;
      set_scheme_variables(resolvedF->operands,
			   /*out*/p->formulaToProve->definingFormula);

      // Copy scheme variables
      formula* clone_closure(const formula* f)
      {
	return formula_clone(f, 0);
      }
      p->formulaToProve->operands = clone_operands(resolvedF->operands, 0);
      ast->axiomSchemes = make_proof_list(p, ast->axiomSchemes);
      return 1;
    }

  // Check p's formula to prove, which may not use p's
  // local operators or variables.
  if (!resolve_names(p->formulaToProve,
		     ast->constants,
		     ast->operators,
		     0, 0, 0,
		     0, 0))
    {
      // finish the error message
      printf("in formula ");
      print_formula(p->formulaToProve);
      printf("\n");
      return 0;
    }

  return 1;
}

short semantic_check(struct folAST* ast)
{
  // First check ast's operator definitions
  /* short opDefsOk = 1; */
  /* void all_ops_ok(const void* nodep, VISIT value, int level) */
  /* { */
  /*   if (value == preorder || value == postorder) */
  /*     return; */

  /*   formula* op = *(formula**)nodep; */

  /*   if (op->file && strcmp(op->file, ast->file) != 0) */
  /*     return; // operator coming from EXTENDS statement, was already checked in its own module */

  /*   const struct formula_list* proofLocalDecl = 0; // not inside a proof */
  /*   opDefsOk &= semantic_check_operator_definition(op, */
  /* 						   ast->operators, */
  /* 						   ast->constants, */
  /* 						   proofLocalDecl); */
  /* } */
  /* twalk(ast->operators, all_ops_ok); // TODO resolve in line order, for op_type */
  /* if (!opDefsOk) */
  /*   return 0; */
  const struct formula_list* proofLocalDecl = 0; // not inside a proof */
  for (struct formula_list* op = ast->operators_by_line; op; op = op->next)
    if (!semantic_check_operator_definition(op->formula_elem,
					    ast->operators,
					    ast->constants,
					    proofLocalDecl))
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

  // TODO use axioms to type primitive operators (relations or operations).
  // If a primitive operator s has no axiom or cannot be typed, refuse it
  // and ask for an additional axiom
  // \A x : s(x) = s(x)   or   \A x : s(x) <=> s(x)

  return proofsOk;
}

