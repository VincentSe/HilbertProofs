#include "proof.h"
#include "stdlib.h"
#include "stdio.h"
#include "string.h"
#include <search.h>

void remove_list_node(struct FormulaDList* l)
{
  // Remove l from its list and make it a singleton list
  if (l->next)
    l->next->previous = l->previous;
  if (l->previous)
    l->previous->next = l->next;
  l->previous = 0;
  l->next = 0;
}

struct FormulaDList* push_justified_formula(struct JustifiedFormula* jf,
					    struct FormulaDList* next)
{
  struct FormulaDList* fl = malloc(sizeof(struct FormulaDList));
  fl->jf = jf;
  fl->next = next;
  fl->previous = 0;
  if (next)
    next->previous = fl;
  return fl;
}

void print_justified_formula(struct JustifiedFormula* jf)
{
  print_formula(jf->formula);
  printf(" BECAUSE %s \n", reason_kind_to_string(jf->reason->rk));
}

struct reason* make_reason(enum reason_kind k,
			   formula* f)
{
  struct reason* reason = malloc(sizeof(struct reason));
  reason->rk = k;
  reason->formula = f;
  return reason;
}

void f_list_free(struct FormulaDList* l)
{
  if (!l) return;
  justified_formula_free(l->jf);
  f_list_free(l->next);
  free(l);
}

proof* make_proof(enum reason_kind proofGoal,
		  formula* formulaToProve,
		  struct string_list* variables,
		  struct FormulaDList* cumulativeTruths)
{
  proof* proof = malloc(sizeof(struct proofS));
  proof->goal = proofGoal;
  proof->formulaToProve = formulaToProve;
  proof->variables = variables;
  proof->cumulativeTruths = cumulativeTruths;
  return proof;
}

void proof_free(proof* p)
{
  if (!p) return;
  //printf("PROOF_FREE "); print_formula(p->formulaToProve); printf("\n");

  formula_free(p->formulaToProve);
  string_list_free(p->variables);

  if (p->cumulativeTruths)
    {
      // Reverse free so that the local operators are still alive
      // when formulas that reference them are freed
      struct FormulaDList* l = p->cumulativeTruths;
      while (l->next)
	l = l->next; // find the end of the list
      while (l)
	{
	  if (!l->jf->reason ||
	      (l->jf->reason->rk == propoTautology && !l->jf->reason->formula))
	    {
	      // local operator or propositional tautology
	      formula_free(l->jf->formula->definingFormula);
	      l->jf->formula->definingFormula = 0;
	    }
	  justified_formula_free(l->jf);
	  struct FormulaDList* prev = l->previous;
	  free(l);
	  l = prev;
	}
    }
  free(p);
}

void justified_formula_free(struct JustifiedFormula* jf)
{
  if (!jf) return;
  formula_free(jf->formula);
  reason_free(jf->reason);
  free(jf);
}

void reason_free(struct reason* r)
{
  if (!r) return;
  formula_free(r->formula);
  free(r);
}

struct JustifiedFormula* make_jf(formula* f, struct reason* reason)
{
  struct JustifiedFormula* jf = malloc(sizeof(struct JustifiedFormula));
  jf->formula = f;
  jf->reason = reason;
  return jf;
}

const char* reason_kind_to_string(enum reason_kind rk)
{
  switch (rk)
    {
    case propoTautology: return "propositional tautology";
    case modusPonens: return "modus ponens";
    case generalization: return "generalization";
    case theorem: return "theorem";
    case axiom: return "axiom";
    case forallInstance: return "instance of forall";
    case existInstance: return "instance of exists";
    case reasonChoose: return "choose";
    };
  printf("Unknown reason kind %d\n", rk);
  return 0;
}

int compare_proofs(const void *l, const void *r)
{
  const proof* pl = l;
  const proof* pr = r;
  if (!pl->formulaToProve->name || !pr->formulaToProve->name)
    return 1;  // TODO for formulas without name, use their printed string

  return strcmp(pl->formulaToProve->name, pr->formulaToProve->name);
}

const formula* get_quantified_formula(const formula* f, enum builtin_operator op)
{
  if (f->builtInOp == op)
    return f;
  if (f->definingFormula && f->definingFormula->builtInOp == op)
    return f->definingFormula;
  return (formula*)0;
}

const formula* get_forall(const formula* f)
{
  const formula* all = get_quantified_formula(f, forall);
  return all ? get_first_operand(all) : 0;
}

unsigned char find_equal(const struct FormulaDList* start,
			 const formula* f)
{
  struct FormulaDList* x = start->previous;
  while (x)
    {
      if (formula_equal(f, x->jf->formula, 0, (variable_substitution*)0, 0))
	return 1;
      x = x->previous;
    }
  return 0;
}

/**
   A formula G is deduced by generalization of a formula F when there exists
   a variable x such as G is \A x : F.

   Careful, this is weaker than accepting all implications F => \A x : F.
   If \A x : F is a false closed formula, then the truth of the implication
   F => \A x : F is the same truth as ~F, ie a function of the free variable x.

   In the special case where F is a closed formula, we do have F => \A x : F,
   because it simply states that F => F.
*/
short check_generalization_statement(const struct FormulaDList* statement,
				     const void* operators)
{
  const formula* f = statement->jf->formula;
  while (f = get_forall(f)) // Cut the forall quantifiers at the beginning of statement->jf->formula
    {
      if (find_equal(statement, f))
	return 1; // implicit modus ponens
    }
  printf("%s:%d: Bad generalization\n",
	 statement->jf->formula->file,
	 statement->jf->formula->first_line);
  return 0;
}

short check_mp_cascade(const struct FormulaDList* statement,
		       const formula* propoFormula,
		       variable_substitution* propositionalVariables,
		       const formula* goalPropoFormula,
		       const void* namedFormulas);

unsigned char find_mp_cascade(const struct FormulaDList* statement,
			      const formula* propoFormula,
			      variable_substitution* propositionalVariables,
			      const formula* goalPropoFormula,
			      const void* namedFormulas,
			      int substitutionCount)
{
  const struct FormulaDList* f = statement->previous;
  while (f)
    {
      if (!f->jf->reason)
	{
	  f = f->previous;
	  continue; // skip local operator definitions
	}
    
      const formula* firstHypothesis = get_first_operand(propoFormula); // in the chain of implications
      unsigned char success = formula_equal(f->jf->formula,
					    firstHypothesis,
					    (struct string_list*)0,
					    propositionalVariables,
					    1) // modus ponens
	&& check_mp_cascade(statement,
			    get_second_operand(propoFormula), // proven by modus ponens
			    propositionalVariables,
			    goalPropoFormula,
			    namedFormulas);
      propositionalVariables[substitutionCount].variable = (char*)0;
      if (success)
	return 1;
      f = f->previous;
    }
  return 0;
}

short check_mp_cascade(const struct FormulaDList* statement,
		       const formula* propoFormula,
		       variable_substitution* propositionalVariables,
		       const formula* goalPropoFormula,
		       const void* namedFormulas)
{
  // Assume : statement->jf->formula is an instance of goalPropoFormula.
  // Assume : propoFormula is a chain of implications leading to
  // goalPropoFormula.
  // Assume : the instantiated propoFormula is proven, either as a tautology
  // or a as modus ponens.

  if (propoFormula == goalPropoFormula)
    return 1; // the goal is proven

  // Save the end of the conclusion's substitutions, because formula_prefix
  // below will modify substitutions.
  variable_substitution* propoEnd = propositionalVariables;
  int substitutionCount = 0;
  while (propoEnd->variable)
    {
      propoEnd++;
      substitutionCount++;
    }

  return find_mp_cascade(statement, propoFormula, propositionalVariables,
			 goalPropoFormula, namedFormulas, substitutionCount);
}

short implicit_propositional_tautology(const struct FormulaDList* statement,
				       const formula* propoTautology,
				       const void* namedFormulas)
{
  // check_propositional_tautology_statement_one failed so statement is not
  // an instance of propoTautology. Try to instantiate a smaller part
  // of propoTautology and prove the rest by modus ponens.

  if (propoTautology->builtInOp != limplies)
    return 0; // modus ponens can only be used on implications

  const formula* propoTautConclusion = propoTautology;
  variable_substitution propositionalVariables[16];
  short found = 0;
  while (propoTautConclusion->builtInOp == limplies)
    {
      propoTautConclusion = get_second_operand(propoTautConclusion); // no need to test formula_prefix on propoTautology, check_propositional_tautology_statement_one already tried it.
      propositionalVariables[0].variable = (char*)0;
      if (formula_equal(statement->jf->formula, propoTautConclusion,
			(struct string_list*)0,
			/*out*/propositionalVariables, 1))
	{
	  found = 1;
	  break;
	}
    }

  // The previous loop can fail if propoTautology doesn't have a second
  // operand chain of implications. It can also succeed on a final
  // propositional variable, as in ~~a => a, for which the rest of
  // the code below will search ~~a among the previous proven formulas.
  if (!found)
    return 0;

  return check_mp_cascade(statement,
			  propoTautology,
			  propositionalVariables,
			  propoTautConclusion,
			  namedFormulas);
}

short check_propositional_tautology_statement(const struct FormulaDList* statement,
					      const proof_set assumedProofs,
					      const formula_set operators,
					      const struct formula_list* proofOperators)
{
  formula* tauto = statement->jf->reason->formula;
  proof searchP;
  searchP.formulaToProve = tauto;
  const proof* tautoProof = proof_set_find(&searchP, assumedProofs);
  if (tautoProof && tautoProof->goal == propoTautology)
    tauto = tautoProof->formulaToProve;
  else
    {
      // Search a local tautology instead
      formula* l = (formula*)find_formula_same_name(proofOperators, tauto);
      if (!l)
	{
	  printf("%s:%d: unknown tautology %s\n",
		 tauto->file,
		 tauto->first_line,
		 tauto->name);
	  return 0;
	}
      tauto = l;
    }

  if (check_propositional_tautology_statement_one(statement->jf->formula, tauto->definingFormula, operators)
      || implicit_propositional_tautology(statement, tauto->definingFormula, operators))
    return 1;

  printf("%s:%d: tautology %s does not match\n",
	 statement->jf->formula->file,
	 statement->jf->formula->first_line,
	 tauto->name);
  return 0;
}

unsigned char find_implicit_modus_ponens(enum reason_kind rk,
					 const struct FormulaDList* statement,
					 const formula_set operators)
{
  struct FormulaDList* x = statement->previous;
  while (x)
    {
      const struct JustifiedFormula* forallFormula = x->jf;
      // Make formula (forallFormula => statement) and check whether
      // it is a valid forall instance.
      formula f;
      f.builtInOp = limplies;
      struct formula_list firstOperand;
      f.operands = &firstOperand;
      firstOperand.formula_elem = forallFormula->formula;
      struct formula_list secondOperand;
      firstOperand.next = &secondOperand;
      secondOperand.formula_elem = statement->jf->formula;
      secondOperand.next = 0;
      if (check_quantifier_instance_statement_one(rk,
						  &f,
						  statement->jf->reason->formula->operands,
						  operators))
	return 1;
      x = x->previous;
    }
  return 0;
}

short check_quantifier_instance_statement(enum reason_kind rk,
					  const struct FormulaDList* statement,
					  const formula_set operators)
{
  // TODO check that the substitution is a term, not a formula.
  // Impossible if the substitution is a user-defined symbol :(
  // \A x : \E y : x = y
  // \E y : ({} \in {{}}) = y

  if (check_quantifier_instance_statement_one(rk,
					      statement->jf->formula,
					      statement->jf->reason->formula->operands,
					      operators))
    return 1;

  // Try to prove statement as BECAUSE MODUS_PONENS instead of BECAUSE \A.
  // For that, search a universal quantification (\A x : F) among the previously
  // proven formulas, such that statement equals F(x <- t).
  // If a formula G equivalent to (\A x : F) is found, the proof is considered to be
  // G   BECAUSE ?;
  // G <=> (\A x : F)   BECAUSE ?;
  // \A x : F   BECAUSE MODUS_PONENS;
  // (\A x : F) => F(x <- t)   BECAUSE \A(t);
  // statement   BECAUSE MODUS_PONENS;

  if (!find_implicit_modus_ponens(rk, statement, operators))
    {
      printf("%s:%d: Bad %s instance ",
	     statement->jf->formula->file,
	     statement->jf->formula->first_line,
	     rk == forallInstance ? "forall" : "exists");
      print_formula(statement->jf->formula);
      printf("\n");
      return 0;
    }

  return 1;
}

const formula* imply_statement(const formula* conclusion,
			       const formula* f)
{
  if (f->builtInOp == limplies)
    return formula_equal(conclusion,
			 get_second_operand(f),
			 0,0,0) ? get_first_operand(f) : 0;

  if (f->builtInOp == lequiv)
    {
      if (formula_equal(conclusion,
			get_second_operand(f),
			0,0,0))
	return get_first_operand(f);
      if (formula_equal(conclusion,
			get_first_operand(f),
			0,0,0))
	return get_second_operand(f);
    }
  return 0;
}

short check_modus_ponens_statement(const struct FormulaDList* statement,
				   const void* namedFormulas)
{
  // Find both an implication concluding statement and the hypothesis of
  // this implication. They can appear in any order, so the algorithmic
  // complexity is a double loop on the previous statements.

  for (const struct FormulaDList* x = statement->previous; x; x = x->previous)
    {
      const struct JustifiedFormula* impl = x->jf;
      // Check that impl is an implication or equivalence concluding statement->jf->formula
      const formula* hypo = imply_statement(statement->jf->formula, impl->formula);
      if (!hypo)
	  continue;
      
      // Find the hypothesis of this implication
      for (struct FormulaDList* hyp = statement->previous; hyp; hyp = hyp->previous)
	{
	  if (hyp->jf->reason // skip local operator definitions
	      && formula_equal(hypo,
			       hyp->jf->formula,
			       0, 0, 0))
	    return 1;
	}
    }

  printf("%s:%d: Bad modus ponens : ",
	 statement->jf->formula->file,
	 statement->jf->formula->first_line);
  print_formula(statement->jf->formula);
  return 0;
}

const formula* parse_equalities(const formula* f, /*out*/variable_substitution* subs)
{
  // Parse the forall quantifiers
  char* variables[8]; // use subs instead ?
  unsigned char vCount = 0;
  const formula* impl = f;
  while (impl->builtInOp == forall)
    {
      variables[vCount] = impl->name;
      vCount++;
      impl = get_first_operand(impl);
    }
  if (vCount & 1)
    return 0; // the number of variables must be even

  if (impl->builtInOp != limplies)
    return 0;
  const formula* equiv = get_second_operand(impl);
  if (equiv->builtInOp != lequiv && equiv->builtInOp != equal)
    return 0;
  
  const formula* equalities = get_first_operand(impl); // x = a /\ y = b

  // Logical ands associate to the left, so start from the end
  unsigned char i = 0;
  while (i < vCount)
    {
      const formula* eq;
      switch (equalities->builtInOp)
	{
	case equal: eq = equalities; break;
	case land: eq = get_second_operand(equalities); break;
	default: eq = 0;
	};
      if (!eq || eq->builtInOp != equal)
	return 0;
      const formula* x = get_first_operand(eq);
      const formula* y = get_second_operand(eq);
      if (x->builtInOp != variable
	  || y->builtInOp != variable
	  || strcmp(variables[vCount-i-2], x->name) != 0 // x
	  || strcmp(variables[vCount-i-1], y->name) != 0) // y
	return 0;
      subs[i/2].variable = x->name;
      subs[i/2].subst = y;
      i += 2;
      equalities = get_first_operand(equalities);
    }
  subs[i/2].variable = (char*)0;
  return equiv; // TODO check variables are distinct
}

/**
   Axiom scheme \A x1 : \A y1 : ... : \A xK : \A yK :
      (x1 = y1 /\ ... /\ xK = yK) => (s <=> s(x1 <- y1, ..., xK <- yK))
   for all formulas s, and scheme
   \A x1 : \A y1 : ... : \A xK : \A yK :
      (x1 = y1 /\ ... /\ xK = yK) => (t  =  t(x1 <- y1, ..., xK <- yK))
   for all terms t. The substitutions concern the free
   occurrences of variables xI only. The new variables yI
   must remain free in formula s. In a term t, all variables
   are free so it doesn't matter.

   The scrict first-order logic equality axioms are when s
   is a primitive relation symbol, not a formula, and t a
   primitive operator symbol, not a term. The formulas can be
   built by instantiation of \A. For example, to prove that
   (x = y) => (x + 2*x) = (y + 2*y)
   the strict axioms would use
   (x = y /\ a = b) => x + a = y + b     by the symbol +
   (x = y /\ a = b) => x * a = y * b     by the symbol *
   then
   (2 = 2 /\ x = y) => 2 * x = 2 * y   BECAUSE \A(x <- 2, a <- x, y <- 2, b <- y);
   x = y => 2 * x = 2 * y   BECAUSE 2 = 2;
   (x = y /\ 2*x = 2*y) => x + 2*x = y + 2*y    BECAUSE \A(x <- x, a <- 2*x, y <- y, b <- 2*y);
   (x = y /\ 2*x = 2*y) => x + 2*x = y + 2*y    BECAUSE TI;

   To go from symbols s to all formulas, we must be careful
   with quantifiers, otherwise we would take as an axiom :
   x = y => ((\A y : x \subseteq y) <=> \A y : y \subseteq y)
   which implies that False <=> True.

   But since we only rename free variables (the new variables
   remain free), for any formula s the formula
   \A x1 : \A y1 : ... : \A xK : \A yK :
      (x1 = y1 /\ ... /\ xK = yK) => (s <=> s(x1 <- y1, ..., xK <- yK))
   is true in all models : formulas s and s(x1 <- y1, ..., xK <- yK) are
   interpreted by the same function in each model. By G�del's
   completeness theorem it is provable.

   Some free variables of formula s can be absent in the xI :
   those stay free with the same name.
*/
unsigned char rename_free_variables_scheme(const formula* f)
{
  variable_substitution subs[8];
  const formula* equiv = parse_equalities(f, /*out*/subs);
  return equiv &&
    formula_equal(get_second_operand(equiv),
		  get_first_operand(equiv),
		  0, subs, 0);
}

short equality_axiom(const formula* f)
{
  if (rename_free_variables_scheme(f))
    return 1;
  
  // axiom x = x, where x is a term
  const formula* firstOp = get_first_operand(f);
  const formula* secondOp = get_second_operand(f);

  if (firstOp && secondOp && f->builtInOp == equal
      && formula_equal(firstOp, secondOp, 0, 0, 0))
    return 1;

  // axiom (x = y /\ x = z) => y = z, where x, y and z are terms
  // and also (y = x /\ z = x) => y = z
  const formula* firstFirstOp = get_first_operand(firstOp);
  const formula* firstSecondOp = get_second_operand(firstOp);
  const formula* secondSecondOp = get_second_operand(secondOp);
  const formula* secondFirstOp = get_first_operand(secondOp);
  if (firstFirstOp && firstSecondOp && secondSecondOp && secondFirstOp)
    {
      // axiom x = y => y = x, where x and y are terms
      if (f->builtInOp == limplies
	  && firstOp->builtInOp == equal
	  && secondOp->builtInOp == equal
	  && formula_equal(firstFirstOp, secondSecondOp, 0, 0, 0)
	  && formula_equal(firstSecondOp, secondFirstOp, 0, 0, 0))
	return 1;

      const formula* firstFirstFirstOp = get_first_operand(firstFirstOp);
      const formula* firstFirstSecondOp = get_second_operand(firstFirstOp);
      const formula* firstSecondFirstOp = get_first_operand(firstSecondOp);
      const formula* firstSecondSecondOp = get_second_operand(firstSecondOp);
      if (f->builtInOp == limplies
	  && firstFirstFirstOp && firstFirstSecondOp && firstSecondFirstOp && firstSecondSecondOp
	  && secondOp->builtInOp == equal
	  && firstFirstOp->builtInOp == equal
	  && firstSecondOp->builtInOp == equal
	  && ((formula_equal(firstFirstFirstOp, firstSecondFirstOp, 0, 0, 0) // x
	       && formula_equal(firstFirstSecondOp, secondFirstOp, 0, 0, 0)
	       && formula_equal(firstSecondSecondOp, secondSecondOp, 0, 0, 0))
	      || (formula_equal(firstFirstFirstOp, secondFirstOp, 0, 0, 0) // y
		  && formula_equal(firstFirstSecondOp, firstSecondSecondOp, 0, 0, 0) // x
		  && formula_equal(firstSecondFirstOp, secondSecondOp, 0, 0, 0)))) // z
	return 1;
    }

  printf("%s:%d: ", f->file, f->first_line);
  print_formula(f);
  printf(" is not an instance of an equality axiom scheme\n");
  return 0;
}

short is_forall(const formula* f,
		const char* x,
		const formula* p,
		const formula* q)
{
  // Test that f is (\A x : p => q)
  const formula* quant = get_first_operand(f);
  return f->builtInOp == forall
    && strcmp(x, f->name) == 0
    && quant->builtInOp == limplies
    && formula_equal(p,
		     get_first_operand(quant),
		     0,0,0)
    && formula_equal(q,
		     get_second_operand(quant),
		     0,0,0);
}

unsigned char match_parallel_quantifiers(const formula* f,
					 /*out*/char** x,
					 /*out*/const formula** p,
					 /*out*/const formula** q)
{
  // Test that f is (\E x : p) => (\E x : q) or forall
  if (!f || (f->builtInOp != limplies && f->builtInOp != lequiv))
    return 0;

  const formula* secondOp = get_second_operand(f);

  *p = get_quantified_formula(get_first_operand(f), forall);
  *q = get_quantified_formula(secondOp, forall);
  if (!*p || !*q)
    {
      *p = get_quantified_formula(get_first_operand(f), exists);
      *q = get_quantified_formula(secondOp, exists);
    }

  if (!*p || !*q
      || strcmp((*p)->name, (*q)->name) != 0) // different quantified variables
    return 0;
  *x = (*p)->name;

  *p = get_first_operand(*p);
  *q = get_first_operand(*q);
  return 1;
}

unsigned char find_impl(const struct FormulaDList* statement,
			const formula* p,
			const formula* q)
{
  for (const struct FormulaDList* x = statement->previous; x; x = x->previous)
    {
      const struct JustifiedFormula* f = x->jf;
      // When using a previously proven formula, the initial \A is optional, drop it
      const formula* hypo = f->formula->builtInOp == forall ? get_first_operand(f->formula) : f->formula;
      unsigned char success = (hypo->builtInOp == statement->jf->formula->builtInOp)
	&& formula_equal(p,
			 get_first_operand(hypo),
			 0,0,0)
	&& formula_equal(q,
			 get_second_operand(hypo),
			 0,0,0);
      if (success)
	return 1;
    }
  return 0;
}


/**
   axiom scheme : (\A x : p => q)  =>  ( (\E x : p) => (\E x : q) )
   and scheme     (\A x : p => q)  =>  ( (\A x : p) => (\A x : q) )

   Could be deduced as
   (\A x : p => q) => (p => q)   BECAUSE \A(x <- x);
   (p => q) => (~q => ~p)   BECAUSE Contraposition;
   (\A x : p => q) => (~q => ~p) BECAUSE TransitImplication;
   (\A x : ~q) => ~q   BECAUSE \A(x <- x);
   (~q => ~p) => ((\A x : ~q) => ~p)   BECAUSE TransitImplication;
   (\A x : p => q) => ((\A x : ~q) => ~p)   BECAUSE TransitImplication;
   \A x : (\A x : p => q) => ((\A x : ~q) => ~p)   BECAUSE GENERALIZATION;
   (\A x : p => q) => (\A x : (\A x : ~q) => ~p)   BECAUSE AXIOM_SCHEME;
   (\A x : (\A x : ~q) => ~p) => ((\A x : ~q) => (\A x : ~p))   BECAUSE AXIOM_SCHEME;
   (\A x : p => q) => ((\A x : ~q) => (\A x : ~p))   BECAUSE TransitImplication;
   ((\A x : ~q) => (\A x : ~p)) => (~(\A x : ~p) => ~(\A x : ~q))   BECAUSE Contraposition;
   (\A x : p => q) => (~(\A x : ~p) => ~(\A x : ~q))   BECAUSE TransitImplication;
   (\A x : p => q) => ((\E x : p) => (\E x : q))   BECAUSE TransitImplication;

   Can be deduced as
   p => q   BECAUSE HYPOTHESIS;
   (\A x : p) => p   BECAUSE \A(x);
   (p => q) => ((\A x : p) => q)   BECAUSE TransitImplication;
   (\A x : p) => q   BECAUSE MODUS_PONENS;
   \A x : (\A x : p) => q   BECAUSE GENERALIZATION;
   (\A x : (\A x : p) => q) => ((\A x : p) => \A x : q)   BECAUSE AXIOM_SCHEME;
   (\A x : p) => (\A x : q)   BECAUSE MODUS_PONENS;
*/
unsigned char add_quantifiers_axiom_schemes(const struct FormulaDList* statement)
{
  char* x;
  const formula *p, *q;

  // Try the full one-line version
  if (match_parallel_quantifiers(get_second_operand(statement->jf->formula),
				 /*out*/&x, /*out*/&p, /*out*/&q)
      && is_forall(get_first_operand(statement->jf->formula), x, p, q))
    return 1;

  // Try implicit modus ponens
  return match_parallel_quantifiers(statement->jf->formula,
				    /*out*/&x, /*out*/&p, /*out*/&q)
    && find_impl(statement, p, q);
}

unsigned char find_forall(const struct FormulaDList* statement,
			  const formula* quant,
			  const formula* firstF)
{
  for (const struct FormulaDList* x = statement->previous; x; x = x->previous)
    {
      const struct JustifiedFormula* jf = x->jf;
      const formula* firstJF = get_first_operand(jf->formula); // p => q
      unsigned char success = jf->formula->builtInOp == quant->builtInOp
	&& firstJF->builtInOp == limplies
	&& strcmp(jf->formula->name, quant->name) == 0 // same quantified variable
	&& formula_equal(firstF,
			 get_first_operand(firstJF), // p
			 0,0,0)
	&& formula_equal(get_first_operand(quant),
			 get_second_operand(firstJF), // q
			 0,0,0)
	&& is_bound_variable(firstF, quant->name);
      if (success)
	return 1;
    }
  return 0;
}


short quantifier_axiom_schemes(const struct FormulaDList* statement)
{
  const formula* f = statement->jf->formula;

  // axiom scheme : (\E x : p) <=> ~(\A x : ~p)

  const formula* firstF = get_first_operand(f);
  const formula* secondF = get_second_operand(f);
  if (!firstF || !secondF)
    return 0;

  if (firstF->builtInOp == lnone && !firstF->operands)
    firstF = firstF->definingFormula;
  if (secondF->builtInOp == lnone && !secondF->operands)
    secondF = secondF->definingFormula;

  const formula* firstFirstF = get_first_operand(firstF);
  const formula* firstSecondF = get_first_operand(secondF);
  if (!firstFirstF || !firstSecondF)
    return 0;

  const formula* firstFirstSecondF = get_first_operand(firstSecondF);

  if (f->builtInOp == lequiv
      && firstF->builtInOp == exists
      && secondF->builtInOp == lnot
      && firstSecondF->builtInOp == forall
      && strcmp(firstF->name, firstSecondF->name) == 0
      && formula_equal(firstFirstF,
		       get_first_operand(firstFirstSecondF),
		       0,0,0))
    return 1;

  if (add_quantifiers_axiom_schemes(statement))
    return 1;

  /* 
     axiom scheme : (\A x : p => q) => (p => \A x : q)
     and scheme     (\E x : p => q) => (p => \E x : q)
     when varibale x has no free occurrences in p.

     It is fine to use equivalent defining formulas in
     formula_equal, because they never introduce free variables.

     Only the universal scheme is a rule of first-order logic,
     the existential can be deduced as
     (\A x : ~q) => ~q   BECAUSE \A(a);
     q => \E x : q   BECAUSE Contraposition;
     p => (q => \E x : q)   BECAUSE PT1;
     (p => q) => (p => \E x : q)   BECAUSE PT2;
     ~(p => \E x : q) => ~(p => q)   BECAUSE Contraposition;
     \A x : ~(p => \E x : q) => ~(p => q)   BECAUSE GENERALIZATION;
     ~(p => \E x : q) => \A x : ~(p => q)   BECAUSE AXIOM_SCHEME; (x has no free occurrences in ~(p => \E x : q))
     (\E x : p => q) => (p => \E x : q)   BECAUSE Contraposition;
  */
  const formula* quant = get_quantified_formula(secondF, forall);
  if (!quant)
    quant = get_quantified_formula(secondF, exists);

  if (f->builtInOp == limplies && quant && find_forall(statement, quant, firstF))
    {
      return 1;
    }

  /* axiom scheme : (\E x : p) => p
     when varibale x has no free occurrences in p.

     Can be deduced as
     ~p => ~p   BECAUSE PT;
     \A x : ~p => ~p   BECAUSE GENERALIZATION;
     ~p => \A x : ~p   BECAUSE AXIOM_SCHEME; (x has no free occurrences in ~p)
     (\E x : p) => p   BECAUSE Contraposition;
  */
  if (f->builtInOp == limplies
      && firstF->builtInOp == exists
      && formula_equal(firstFirstF,
		       secondF,
		       0,0,0))
    return 1;

  return 0;
}

short check_axiom_statement(const struct JustifiedFormula* jf,
			    const void* assumedProofs,
			    const void* operators,
			    const struct formula_list* proofOperators)
{
  // search for a declared AXIOM in a fol file
  proof searchP;
  searchP.formulaToProve = jf->formula;
  const proof** otherProof = tfind(&searchP, (void**)&assumedProofs, compare_proofs);
  if (otherProof && (*otherProof)->goal == axiom)
    return 1;

  // then search operators' defining axioms, like
  // x \subseteq y <=> (\A z : z \in x => z \in y)
  const formula* firstOp = get_first_operand(jf->formula);
  if (jf->formula->builtInOp == lequiv && is_custom_operator(firstOp))
    {
      const formula* defF = get_second_operand(jf->formula);
      formula** defOp = tfind(firstOp,
			      (void**)&operators,
			      formula_compare_operators);
      if (defOp && formula_equal((*defOp)->definingFormula,
				 defF,
				 0, 0, 0))
	{
	  return 1;
	}

      const struct formula_list* proofLoc = proofOperators;
      while (proofLoc)
	{
	  if (formula_equal(defF, proofLoc->formula_elem->definingFormula, 0, 0, 0))
	    return 1;
	  proofLoc = proofLoc->next;
	}
    }

  if (!otherProof || (*otherProof)->goal != axiom)
    {
      printf("%d: ", jf->formula->first_line);
      print_formula(jf->formula);
      printf(" is not an axiom\n");
      return 0;
    }
  return 1;
}

unsigned char find_not_substituted(const struct formula_list* statement,
				   unsigned int substCount,
				   variable_substitution* substitutions)
{
  for (; statement; statement = statement->next)
    {
      const formula* op = statement->formula_elem;
      unsigned char isSubst = 0;
      for (int i=0; i<substCount; i++)
	if (strcmp(op->name, substitutions[i].variable) == 0)
	  {
	    isSubst = 1;
	    break;
	  }
      if (!isSubst)
	return 1;
    }
  return 0;
}

unsigned char check_scheme_instance_one(const struct FormulaDList* statement,
					const proof* scheme)
{
  variable_substitution substitutions[2];
  substitutions[0].variable = (char*)0;
  if (!formula_equal(statement->jf->formula,
		     scheme->formulaToProve->definingFormula, // contains a formula variable F
		     (struct string_list*)0,
		     /*out*/ substitutions, // find a substitution for F
		     1))
    return 0;

  // Check all scheme variables were substituted, and no other variable
  unsigned int substCount = 0;
  while (substitutions[substCount].variable)
    substCount++;
  if (substCount != formula_list_size(scheme->formulaToProve->operands)
      || find_not_substituted(scheme->formulaToProve->operands,
			      substCount,
			      substitutions))
    return 0;

  // Check all forbidden variables are bound
  const struct string_list* var = scheme->variables;
  while (var)
    {
      if (!is_bound_variable(substitutions[0].subst, var->string_elem))
	return 0; // cannot print an error message : another axiom scheme might succeed, validating statement
      var = var->next;
    }
  return 1;
}

short check_axiom_scheme_statement(const struct FormulaDList* statement,
				   const struct proof_list* axiomSchemes)
{
  // Search for a declared AXIOM_SCHEME in a fol file
  // and get its substituted formula.
  // Those only have one formula argument.
  for (const struct proof_list* schemes = axiomSchemes; schemes; schemes = schemes->next)
    if (check_scheme_instance_one(statement, schemes->proof_elem))
      return 1;

  printf("%s:%d: ",
	 statement->jf->formula->file,
	 statement->jf->formula->first_line);
  print_formula(statement->jf->formula);
  printf(" is not an instance of an axiom scheme\n");
  return 0;
}

/**
   Let T be a theory. When defining on top of T,
   someNewOp(x,y,z) == CHOOSE t : P(t,x,y,z)
   it inroduces a new ternary operator someNewOp and an axiom for it,
   \A x : \A y : \A z : (\E t : P(t,x,y,z)) => P(someNewOp(x,y,z),x,y,z)

   For example, the empty set :
   {} == CHOOSE t : \A x : x \notin t

   By a general rule of the existential quantifier,
   P(someNewOp(x,y,z),x,y,z) => (\E t : P(t,x,y,z))   BECAUSE \E(t <- someNewOp(x,y,z));
   so the previous axiom actually proves the equivalence :
   (\E t : P(t,x,y,z)) <=> P(someNewOp(x,y,z),x,y,z)

   Let T+ be the extension of T by someNewOp and its axiom. Any model M of T
   can be extended into a model M+ of T+ by
      - the same universe U
      - the interpretation of someNewOp as an application U^3 -> U such that
         - when M satisfies \E t : P(t,x,y,z), someNewOp(x,y,z) is interpreted
	   as one of those t's in U
	 - otherwise someNewOp(x,y,z) is interpreted as any element of U.
   The axiom above is satisfied in M+.

   By G�del's completeness theorem, if T+ has a contradiction then so does T
   (neither has models). Put differently, the introduction of operator 
   someNewOp does not introduce contradictions.

   Can T+ prove formulas of T that are undecidable in T ? An undecidable
   formula F of T assumes T is consistent (otherwise T proves every formula).
   By G�del's completeness theorem, T has models, some in which F is true
   and some in which F is false. Take a model M of T where F is false.
   In the extended model M+, F is still false because model extensions
   preserve truth values. Hence T+ does not prove F.

   Syntactically, T+ proves a formula G involving someNewOp(x,y,z) if
   and only if T proves the formula
      (\A t : G(someNewOp(x,y,z) <- t))
   \/ ((\E t : P(t,x,y,z)) /\ \A t : P(t,x,y,z) => G(someNewOp(x,y,z) <- t))
   where someNewOp(x,y,z) is removed, replaced by t. To see that,
   assume that T+ proves G and let M a model of T. If M satisfies
   \E t : P(t,x,y,z), we can extend to M+ by interpreting someNewOp(x,y,z)
   with any such t. Any such M+ satisfies G because any model of T+ satisfies G.
   So M+ satisfies \A t : P(t,x,y,z) => G(someNewOp(x,y,z) <- t),
   which only uses interpretations of M.
   If M does not satisfy \E t : P(t,x,y,z), we can extend to M+ by
   interpreting someNewOp(x,y,z) with any value and G will be true.
   This means that M satisfies \A t : G(someNewOp(x,y,z) <- t).

   Conversely, assume T proves the disjunction above. Then in T+ we have,
   (\A t : G(someNewOp(x,y,z) <- t)) => G   BECAUSE \A(t <- someNewOp(x,y,z));
   (\E t : P(t,x,y,z)) => P(someNewOp(x,y,z),x,y,z)   BECAUSE CHOOSE someNewOp;
   (\A t : P(t,x,y,z) => G(someNewOp(x,y,z) <- t))
      => (P(someNewOp(x,y,z),x,y,z) => G)   BECAUSE \A(t <- someNewOp(x,y,z));
   ((\E t : P(t,x,y,z)) /\ (\A t : P(t,x,y,z) => G(someNewOp(x,y,z) <- t)))
      => (P(someNewOp(x,y,z),x,y,z) /\ (P(someNewOp(x,y,z),x,y,z) => G))
      BECAUSE MergeImplicationsAnd;
   (P(someNewOp(x,y,z),x,y,z) /\ (P(someNewOp(x,y,z),x,y,z) => G))
      => G   BECAUSE MODUS_PONENS;
   ((\E t : P(t,x,y,z)) /\ (\A t : P(t,x,y,z) => G(someNewOp(x,y,z) <- t)))
      => G   BECAUSE TI;
   G   BECAUSE CombineImplicationsStart + MODUS_PONENS;   
*/
short check_choose_statement(const formula* f,
			     const formula* chooseReason)
{
  // axiom scheme : (\E x : P) => P(CHOOSE x : P)
  // For example the empty set :
  // (\E b : \A x : x \notin b) => (\A x : x \notin {})

  const formula* chooseF = get_quantified_formula(chooseReason, choose);
  if (!chooseF)
    {
      printf("%s:%d: bad choose reason\n", f->file, f->first_line);
      return 0;
    }

  // Compare the reason chooseF and the existential formula
  const formula* firstF = get_second_operand(f);
  const formula* existsF = get_first_operand(f);
  if (!firstF || !existsF
      || f->builtInOp != limplies
      || existsF->builtInOp != exists
      || strcmp(existsF->name, chooseF->name) != 0 // different quantified variables
      || !formula_equal(get_first_operand(chooseF), get_first_operand(existsF), 0, 0, 0))
    {
      printf("%s:%d: bad choose reason\n", f->file, f->first_line);
      return 0;
    }

  // Verify the substitution in the deduced formula
  const formula* firstSecondF = get_first_operand(existsF);
  variable_substitution before[2];
  before[0].variable = existsF->name;
  before[0].subst = chooseReason; // cut its defining formula locally ?
  before[1].variable = (char*)0;
  if (formula_equal(firstF,
		    firstSecondF,
		    (struct string_list*)0,
		    before, 0))
    return 1;

  printf("%s:%d: bad choose reason\n", f->file, f->first_line);
  return 0;
}

// Check XXX BECAUSE THEOREM;
short check_theorem_invocation_statement(const formula* f, const proof_set assumedProofs)
{
  proof searchP;
  searchP.formulaToProve = (formula*)f;
  const proof* otherProof = proof_set_find(&searchP, assumedProofs);
  if (otherProof
      && otherProof->goal == theorem
      && otherProof->cumulativeTruths)
    {
      if (strcmp(f->file, otherProof->formulaToProve->file) == 0
	  && f->first_line < otherProof->formulaToProve->first_line)
	{
	  // Prevent cycles in proofs, to avoid for example giving two names
	  // to the same closed formula and incorrectly proving it
	  // by invoking each other.
	  // Equivalently, invoking a theorem is copying its proof : if there
	  // are cycles, those copies will create an infinite text.
	  printf("%s:%d: Invocation of a theorem proven later\n", f->file, f->first_line);
	  return 0;
	}
      return 1;
    }

  printf("%s:%d: unknown theorem %s\n", f->file, f->first_line, f->name);
  return 0;
}

short check_proof_statement(const struct FormulaDList* statement,
			    const proof* p,
			    const struct formula_list* proofLocalOps,
			    const formula_set operators,
			    const proof_set assumedProofs,
			    const struct proof_list* axiomSchemes)
{
  if (!statement->jf->reason)
    {
      // By bison checking (rule justifiedFormula), a justified formula
      // either has a reason or is an operator definition, in which case
      // there is nothing to check.
      return 1;
    }

  if (statement->jf->reason->rk == propoTautology
      && !statement->jf->reason->formula)
    {
      // Declaration of local propositional tautology, like
      // implyNotAnd(a,b,c) == (a => ~(b /\ c)) => ((a /\ b) => ~c)   PROPO_TAUTO;
      const formula* tauto = statement->jf->formula;
      return is_propositional_formula(tauto)
	&& prove_propositional_tautology(tauto);
    }
  
  switch (statement->jf->reason->rk)
    {
      // In these two cases, the check is just formula_equal between statement->jf->formula
      // and an axiom or theorem formula taken from assumedProofs.
    case axiom:
      return check_axiom_statement(statement->jf, assumedProofs, operators, proofLocalOps);
    case theorem:
      return check_theorem_invocation_statement(statement->jf->formula, assumedProofs);

      // Axiom scheme cases. They check that several subformulas of statement->jf->formula
      // are equal or substituted from one another.
    case axiomScheme:
      return check_axiom_scheme_statement(statement, axiomSchemes);
    case quantifierScheme:
      if (quantifier_axiom_schemes(statement))
	return 1;
      printf("%s:%d: ",
	     statement->jf->formula->file,
	     statement->jf->formula->first_line);
      print_formula(statement->jf->formula);
      printf(" is not an instance of a quantifier axiom scheme\n");
      return 0;
    case equalityScheme:
      return equality_axiom(statement->jf->formula);
    case forallInstance:
    case existInstance:
      return check_quantifier_instance_statement(statement->jf->reason->rk, statement, operators);
    case generalization:
      return check_generalization_statement(statement, operators);
    case propoTautology:
      return check_propositional_tautology_statement(statement, assumedProofs,
						     operators, proofLocalOps);
    case reasonChoose:
      return check_choose_statement(statement->jf->formula, statement->jf->reason->formula);

      // The only checking that looks at the previously proven formulas,
      // to cut proven hypotheses in proven implications.
    case modusPonens:
      return check_modus_ponens_statement(statement, operators);
    };

  printf("Unknown reason kind %s\n", reason_kind_to_string(statement->jf->reason->rk));
  return 0;
}

short semantic_check_operator_definition(formula* op,
					 const formula_set operators,
					 const struct formula_list* constants,
					 const struct formula_list* proofLocalDecl)
{
  // A valid declaration is for example :
  // extensionality == \A a : \A b : (\A x : x \in a <=> x \in b) => a = b

  // By prior syntax check, op->name != 0 and op->builtInOp == lnone
  short success = resolve_names(/*out*/op->definingFormula,
				constants,
				operators,
				(struct string_list*)0,
				op->operands,
				proofLocalDecl);
  return success;

  // TODO Check that op->freeVariables are not quantified in the right-hand side formula
}

short semantic_check_reason(struct reason* r,
			    const proof_set assumedProofs,
			    const proof* p,
			    const struct formula_list* proofLocalOps,
			    const formula_set operators,
			    const struct formula_list* constants)
{
  if (!r->formula)
    return 1; // ok, nothing to check

  if (r->rk == propoTautology)
    return 1; //semantic_check_tautology(r->formula, assumedProofs);

  return resolve_names(/*out*/r->formula,
		       constants,
		       operators,
		       p->variables,
		       (struct formula_list*)0, // no operator variables
		       proofLocalOps);
}

short semantic_check_proof_statement(const struct JustifiedFormula* jf,
				     const formula_set operators,
				     const struct formula_list* constants,
				     const proof_set assumedProofs,
				     const proof* p,
				     struct formula_list** proofLocalOps)
{
  if (jf->reason)
    {
      if (jf->reason->rk == propoTautology && !jf->reason->formula)
	{
	  // local propositional tautology
	  *proofLocalOps = make_formula_list(jf->formula, *proofLocalOps);
	  return resolve_names(jf->formula->definingFormula,
			       constants,
			       operators,
			       (struct string_list*)0,
			       jf->formula->operands, 0);
	}
      return resolve_names(jf->formula,
			   constants,
			   operators,
			   p->variables,
			   0,
			   *proofLocalOps)
	&& semantic_check_reason(jf->reason, assumedProofs, p, *proofLocalOps, operators, constants);
    }
  else
    {
      // A statement without reason in a proof is a local operator.
      // Check it and register it in p->operators.
      if (!semantic_check_operator_definition(jf->formula,
					      operators,
					      constants,
					      *proofLocalOps))
	return 0;
      *proofLocalOps = make_formula_list(jf->formula, *proofLocalOps);
    }

  return 1;
}

short check_proof(const proof* proof,
		  const formula_set operators,
		  const struct formula_list* constants,
		  const proof_set assumedProofs,
		  const struct proof_list* axiomSchemes)
{
  struct formula_list* localOperators = 0; // quicker index to the proof's local operators
  
  switch (proof->goal)
    {
    case axiom:
    case axiomScheme:
      return 1; // an axiom is its own proof, no need to verify it
    case propoTautology:
      return is_propositional_formula(proof->formulaToProve)
	&& prove_propositional_tautology(proof->formulaToProve);
    case theorem:
      if (!proof->cumulativeTruths)
	{
	  printf("%s:%d: there is no proof of theorem ",
		 proof->formulaToProve->file,
		 proof->formulaToProve->first_line);
	  print_formula(proof->formulaToProve);
	  printf("\n");
	  return 0;
	}

      struct FormulaDList* statement = proof->cumulativeTruths;
      struct FormulaDList* lastStatement = 0;
      while (statement
	     && semantic_check_proof_statement(statement->jf, operators, constants,
					       assumedProofs, proof, &localOperators)
	     && check_proof_statement(statement, proof, localOperators,
				      operators, assumedProofs,
				      axiomSchemes))
	{
	  if (!statement->next)
	    lastStatement = statement;
	  statement = statement->next;
	}

      struct formula_list* op = localOperators;
      while (op)
      	{
	  op->formula_elem = (formula*)0;
      	  //formula_free(op->formula_elem->definingFormula);  TODO
      	  //op->formula_elem->definingFormula = (formula*)0;
      	  op = op->next;
      	}
      formula_list_free(localOperators);

      if (!statement)
	{
	  // All steps of the proof were correct
	  if (!formula_equal(lastStatement->jf->formula,
			     proof->formulaToProve, 0, 0, 0))
	    {
	      printf("%s:%d: the proof does not end with its goal\n",
		     proof->formulaToProve->file,
		     lastStatement->jf->formula->first_line);
	      return 0;
	    }

	  printf("%s ", reason_kind_to_string(proof->goal));
	  print_formula(proof->formulaToProve);
	  printf(" proven.\n"); // if there are errors in the proofs, the wrong statement has printed its specialized error message
	  return 1;
	}
    };

  // In case an error in a statement silently returns (bug),
  // complain here once more :
  printf("Error in proof of ");
  print_formula(proof->formulaToProve);
  printf("\n");
  return 0;
}

impl_list_type(proof)
impl_set_type(proof, compare_proofs)
