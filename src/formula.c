#include "formula.h"
#include "stdlib.h"
#include "stdio.h"
#include "string.h"
#include <search.h>

const formula* get_first_operand(const formula* f)
{
  return (f && f->operands) ? f->operands->formula_elem : 0;
}

const formula* get_second_operand(const formula* f)
{
  if (!f || !f->operands)
    return 0;
  const struct formula_list* fl = f->operands->next;
  return fl ? fl->formula_elem : 0;
}

void print_formula(const formula* f)
{
  if (!f)
    {
      printf("Null formula");
      return;
    }

  if (f->builtInOp == variable)
    {
      printf("var %s", f->name);
      return;
    }

  if (f->builtInOp == schemeVariable)
    {
      printf("sVar %s", f->name);
      return;
    }

  if (f->builtInOp == lnone)
    {
      // custom operator
      printf("%s", f->name);
      struct formula_list* operand = f->operands;
      if (operand)
	{
	  printf("(");
	  while (operand)
	    {
	      print_formula(operand->formula_elem);
	      operand = operand->next;
	    }
	  printf(")");
	}
      return;
    }

  if (f->builtInOp == lnot)
    {
      printf("~(");
      print_formula(get_first_operand(f));
      printf(")");
      return;
    }

  if (f->builtInOp == exists
      || f->builtInOp == forall
      || f->builtInOp == choose)
    {
      printf("%s %s (", op_to_string(f->builtInOp), f->name);
      print_formula(get_first_operand(f));
      printf(")");
      return;
    }

  if (f->builtInOp == setEnumerate)
    {
      printf("{}");
      return;
    }
  if (f->builtInOp == tuple)
    {
      printf("<<");
      struct formula_list* operand = f->operands;
      while (operand)
	{
	  print_formula(operand->formula_elem);
	  if (operand->next) printf(", ");
	  operand = operand->next;
	}
      printf(">>");
      return;
    }

  // Binary formula
  printf("(");
  print_formula(get_first_operand(f));
  printf(") %s (", op_to_string(f->builtInOp));
  print_formula(get_second_operand(f));
  printf(")");
}

unsigned char formula_is_term(const formula* f,
			      const formula_set ops)
{
  switch (f->builtInOp)
    {
    case choose:
    case variable:
      return 1;
    case in: // TODO look at axioms using it to know its a relational operator
    case notin:
    case limplies:
    case lnot:
    case lequiv:
    case land:
    case lor:
    case forall:
    case exists:
      return 0;
    }

  if (f->definingFormula)
    return formula_is_term(f->definingFormula, ops);
  formula* opDef = formula_set_find(f, ops);
  if (opDef)
    return formula_is_term(opDef, ops); // even if the variables don't substitute, the type is that of the defining formula
  return 0;
}

const char* op_to_string(enum builtin_operator op)
{
  switch (op)
    {
    case lnone: return "lnone";
    case lnot: return "~";
    case lor: return "\\/";
    case land: return "/\\";
    case limplies: return "=>";
    case lequiv: return "<=>";
    case forall: return "\\A";
    case exists: return "\\E";
    case choose: return "CHOOSE";
    case setEnumerate: return "setEnumerate";
    case setSeparation: return "setSeparation";
    case in: return "\\in";
    case notin: return "\\notin";
    case subset: return "\\subset";
    case equal: return "=";
    case different: return "#";
    case subseteq: return "\\subseteq";
    case binIntersect: return "\\intersect";
    case unaryUnion: return "UNION";
    case powerset: return "SUBSET";
    case plus: return "+";
    };
  printf("Unknown operator %d\n", op);
  return 0;
}

void formula_free(formula* f)
{
  if (!f)
    return;
  //  printf("\n %p FORMULA_FREE ", f); print_formula(f);

  if (f->definingFormula && f->definingFormula->first_line == 0)
    {
      formula_free(f->definingFormula);
    }

  free(f->name);
  formula_list_free(f->operands);
  free(f);
}

int formula_compare_operators(const void *l, const void *r)
{
  // Compare builtInOp first, then names
  const formula* ml = l;
  const formula* mr = r;
  if (ml->builtInOp != mr->builtInOp)
    return mr->builtInOp - ml->builtInOp;
  else if (ml->builtInOp == lnone)
    return strcmp(ml->name, mr->name);
  else if (ml->builtInOp == setEnumerate || ml->builtInOp == tuple)
    {
      // The relation l <= r defined by formula_compare_names(l,r) <= 0
      // is a total order : reflexive, anti-symmetric, transitive and total
      return formula_list_size(mr->operands) - formula_list_size(ml->operands);
    }
  
  return 0;
}

formula* check_operator_definition(formula* def, formula* right)
{
  if (def->builtInOp == lnot || def->builtInOp == lor
      || def->builtInOp == lnot || def->builtInOp == limplies
      || def->builtInOp == lequiv || def->builtInOp == forall || def->builtInOp == exists)
    {
      // cannot redefine logical operators
      return (formula*)0;
    }

  // Check that the left-hand side only has variables
  struct formula_list* operand = def->operands;
  while (operand)
    {
      if (operand->formula_elem->builtInOp != lnone)
	{
	  printf("An operator definition must have depth 1");
	  return 0;
	}
      operand->formula_elem->builtInOp = variable;
      operand = operand->next;
    }
  def->definingFormula = right;
  return def;
}

formula* make_formula(enum builtin_operator builtInOp,
		      const char* name,
		      struct formula_list* operands,
		      const char* file,
		      long first_line)
{
  formula* f = malloc(sizeof(formula));
  f->builtInOp = builtInOp;
  f->name = (char*)name;
  f->operands = operands;
  f->file = file;
  f->first_line = first_line;
  f->definingFormula = 0;

  if (builtInOp == notin || builtInOp == different)
    {
      // formula_prefix must return parts of formulas for substitutions,
      // don't make build construct local negations of formulas, do it here.
      formula* not = malloc(sizeof(formula));
      not->builtInOp = lnot;
      not->name = (char*)0;
      not->operands = make_formula_list(f, 0);
      not->file = file;
      not->first_line = first_line;
      not->definingFormula = 0;
      f->builtInOp = builtInOp == notin ? in : equal;
      return not;
    }

  return f;
}

/**
   Operator that can be defined in a FOL file
*/
short is_custom_operator(const formula* op)
{
  if (op->builtInOp == lnone
      || op->builtInOp == in
      || op->builtInOp == subseteq
      || op->builtInOp == binIntersect
      || op->builtInOp == binUnion
      || op->builtInOp == powerset
      || op->builtInOp == plus
      || op->builtInOp == setEnumerate  // empty set, singleton, pairs, ...
      || op->builtInOp == cartesianProduct
      || op->builtInOp == funcApply
      || op->builtInOp == tuple)
    return 1;

  return 0;
}

/**
   Find a variable v of formula f satisfying predicate pred, which is given
   - the variable v
   - the union of boundVars and all the bound variables of f at v.
*/
const char* find_variable(const formula* f,
			  const struct string_list* boundVars,
			  unsigned char (*pred)(const char* v, const struct string_list* boundVars))
{
  if (f->builtInOp == variable)
    {
      return pred(f->name, boundVars) ? f->name : (const char*)0;
    }

  if (f->builtInOp == forall
      || f->builtInOp == exists
      || f->builtInOp == choose)
    {
      struct string_list bindOneMore; // TODO check if f->name already in boundVars
      bindOneMore.string_elem = f->name;
      bindOneMore.next = (struct string_list*)boundVars;
      return find_variable(get_first_operand(f),
			   &bindOneMore,
			   pred);
    }

  for (const struct formula_list* operand = f->operands; operand; operand=operand->next)
    {
      const char* v = find_variable(operand->formula_elem, boundVars, pred);
      if (v)
	return v;
    }
  return 0;
}

/**
   Search a free variable of f that is also in boundVars.
*/
unsigned char variable_capture(const formula* f,
			       const struct string_list* boundVars)
{
  unsigned char capture(const char* v, const struct string_list* innerBoundVars)
  {
    return !string_list_contains(innerBoundVars, v)
      && string_list_contains(boundVars, v);
  }
  return find_variable(f, 0, capture) != 0;
}

/**
   Test that all occurrences of variable v in formula f are bound
   (which includes the case that v doesn't appear in f).
*/
short is_bound_variable(const formula* f, const char* v)
{
  unsigned char free_occurrence(const char* w, const struct string_list* boundVars)
  {
    return strcmp(v,w) == 0
      && !string_list_contains(boundVars, w);
  }

  return !find_variable(f, 0, free_occurrence);
}

variable_substitution* variable_substitution_find(const char* var,
						  variable_substitution* subst)
{
  variable_substitution* sub = subst;
  if (sub) while (sub->variable)
	     {
	       if (var && strcmp(var, sub->variable) == 0)
		 return sub;
	       sub++;
	     }
  return sub; // the end of substitutions, to append new ones
}

/**
   Test that
   - f equals freeSubs(var)
   - all free variables of f are not in boundVariables

   When substituteMore is true, freeSubs can be extended so that
   the previous 2 conditions are true.
*/
short is_free_substitution(const formula* f,
			   const char* var,
			   const struct string_list* boundVariables,
			   variable_substitution* freeSubs,
			   unsigned char substituteMore)
{
  if (variable_capture(f, boundVariables))
    return 0;
  
  variable_substitution* sub = variable_substitution_find(var, freeSubs);

  if (sub && sub->variable)
    {
      unsigned char freeSubst = formula_equal(f, sub->subst,
					      (const struct string_list*)0,
					      (variable_substitution*)0,
					      0);
      return freeSubst;
    }
  else if (f->builtInOp == variable && strcmp(var, f->name) == 0)
    return 1; // same free variable
  else if (substituteMore && sub)
    {
      // new free variable, register its substitution
      sub->variable = var;
      sub->subst = f;
      sub[1].variable = (char *)0;
      return 1;
    }
  else
    return 0;
}

unsigned char formula_equal(const formula* f,
			    const formula* g,
			    const struct string_list* boundVariables,
			    variable_substitution* freeSubs,
			    unsigned char substituteMore)
{
  if (formula_compare_operators(f, g) == 0
      && f->builtInOp != variable) // 2 variables are not equal when g is substituted
    {
      // Don't use defining formulas in this case, comparing operands
      // is enough and faster.

      if (g->builtInOp == forall
	  || g->builtInOp == exists
	  || g->builtInOp == choose)
	{
	  if (strcmp(f->name, g->name) != 0)
	    return 0; // different quantified variables
	  
	  // Compare operands of g and f with variable g->name bound
	  struct string_list bindVariable;
	  bindVariable.string_elem = g->name;
	  bindVariable.next = (struct string_list*)boundVariables;
	  return formula_equal(get_first_operand(f),
			       get_first_operand(g),
			       &bindVariable,
			       freeSubs,
			       substituteMore);
	}
      else
	{
	  // compare operands
	  const struct formula_list* fOperand = f->operands;
	  const struct formula_list* gOperand = g->operands;
	  while (fOperand)
	    {
	      if (!formula_equal(fOperand->formula_elem,
				 gOperand->formula_elem,
				 boundVariables,
				 freeSubs,
				 substituteMore))
		return 0;
	      fOperand = fOperand->next;
	      gOperand = gOperand->next;
	    }
	  return !gOperand;
	}
    }
  else
    {
      // Different operators or f->builtInOp==variable
      if (g->builtInOp == variable)
	{
	  const unsigned char sameBoundVar = string_list_contains(boundVariables, g->name)
	    && f->builtInOp == variable
	    && strcmp(g->name, f->name) == 0;
	  unsigned char eqVar = sameBoundVar || is_free_substitution(f,
								     g->name,
								     boundVariables,
								     freeSubs,
								     substituteMore);
	  return eqVar;
	}
      else if (g->builtInOp == schemeVariable)
	{
	  // In this case, g->operands are substitutions inside the scheme variable,
	  // such as F(x <- y) in the replacement axiom scheme.
	  // This assumes F(x <- y) occurs after F in the scheme, so that F
	  // is already in freeSubs.
	  variable_substitution* schemeFormulaSubst = freeSubs;
	  while (schemeFormulaSubst->variable)
	    {
	      if (strcmp(schemeFormulaSubst->variable, g->name) == 0)
		break;
	      schemeFormulaSubst++;
	    }
	  
	  if (schemeFormulaSubst->variable)
	    {
	      variable_substitution schemeVarSubst[16];
	      variable_substitution* s = schemeVarSubst;
	      struct formula_list* sub = g->operands;
	      while (sub)
		{
		  s->variable = sub->formula_elem->name;
		  s->subst = sub->next->formula_elem;
		  s++;
		  sub = sub->next->next;
		}
	      s->variable = (char*)0;
	      unsigned char schemeEq = formula_equal(f, schemeFormulaSubst->subst,
						     0, schemeVarSubst,
						     0);
	      return schemeEq;
	    }
	  else
	    {
	      // Substitutions of scheme variables don't need to be free
	      schemeFormulaSubst->variable = g->name;
	      schemeFormulaSubst->subst = f;
	      schemeFormulaSubst[1].variable = (char*)0;
	      return 1;
	    }
	}

      // Try defining formulas last, after we know the true ops don't work
      if (is_custom_operator(f) && f->definingFormula)
	{
	  // Assume f <=> f->definingFormula (which was tested in
	  // resolve_operator_or_variable).
	  // This actually checks that f <=> g, rather than equality of formulas.
	  // freeSubs does not apply to f so it doesn't matter here.
	  return formula_equal(f->definingFormula, g,
			       boundVariables, freeSubs,
			       substituteMore);
	}

      if (is_custom_operator(g) && g->definingFormula && !freeSubs)
	{
	  // Assume g <=> g->definingFormula (which was tested in
	  // resolve_operator_or_variable).
	  // This actually checks that f <=> g, rather than equality of formulas.
	  // PROBLEM : y<-z is a free substitution of x \subseteq y,
	  // yielding x \subseteq z ; but not in \A z : z \in x => z \in y
	  return formula_equal(f, g->definingFormula,
			       boundVariables, freeSubs,
			       substituteMore);
	}
      return 0;
    }
  return 0;
}

void enum_variables(const formula* f,
		    /*out*/char sortedVariables[])
{
  if (f->builtInOp == variable)
    {
      // Insert f at its place in sortedVariables
      char* c = sortedVariables;
      while (*c && *c < *f->name)
	c++;
      if (*c != *f->name)
	{
	  const int len = strlen(sortedVariables) + 1; // include the final 0
	  memmove(/*out*/c + 1, c, len - (c - sortedVariables));
	  *c = *f->name;
	}
      return;
    }

  const struct formula_list* operands = f->operands;
  while (operands)
    {
      enum_variables(operands->formula_elem, /*out*/sortedVariables);
      operands = operands->next;
    }
}

/**
   Check that formula f is only made of logical connectors /\, \/, =>, <=> and ~.
*/
short is_propositional_formula(const formula* f)
{
  struct formula_list* operands = f->operands;
  switch (f->builtInOp)
    {
    case lnone:
      if (!operands) // resolve only aliases
	return is_propositional_formula(f->definingFormula);
    case variable:
      return 1; // propositional variable
    case lnot:
    case lor:
    case land:
    case limplies:
    case lequiv:
      while (operands)
	{
	  if (!is_propositional_formula(operands->formula_elem))
	    return 0;
	  operands = operands->next;
	}
      return 1;
    };
  printf("Invalid operator in propositional formula");
  return 0;
}

/**
   Assume that formula f is propositional (no quantifiers,
   only logical operators) and evaluate it, given values
   for its variables.

   Because of the bitmask, it accepts at most 64 variables.
*/
unsigned char eval_propositional_formula(const formula* f,
					 const char variables[],
					 unsigned long long values) // bit mask
{
  short pos = 0;
  const char* c = variables;
  switch (f->builtInOp)
    {
    case variable:
      while (*c)
	{
	  if (*c == *f->name)
	    return (values & (1 << pos)) != 0; // != 0 to make it boolean
	  pos++;
	  c++;
	}
      printf("Variable not found %c\n", f->name);
      return 0;

    case lnot:
      return !eval_propositional_formula(get_first_operand(f), variables, values);
    case lor:
      return eval_propositional_formula(get_first_operand(f), variables, values)
	|| eval_propositional_formula(get_second_operand(f), variables, values);
    case land:
      return eval_propositional_formula(get_first_operand(f), variables, values)
	&& eval_propositional_formula(get_second_operand(f), variables, values);
    case limplies:
      return !eval_propositional_formula(get_first_operand(f), variables, values)
	|| eval_propositional_formula(get_second_operand(f), variables, values);
    case lequiv:
      return eval_propositional_formula(get_first_operand(f), variables, values)
	== eval_propositional_formula(get_second_operand(f), variables, values);
    };

  return 0; // conservative error case : it will declare that f is not a propositional tautology
}

unsigned char prove_propositional_tautology(const formula* op)
{
  char variables[65];
  variables[0] = '\0';
  enum_variables(op->definingFormula, /*out*/variables);

  if (strlen(variables) > 64)
    {
      printf("More than 64 variables, prove this tautology by text rather than boolean affectations");
      return 0;
    }

  const unsigned long long numPossibilities = 1 << strlen(variables);
  for (unsigned long long values = 0; values < numPossibilities ; values++)
    {
      if (!eval_propositional_formula(op->definingFormula, variables, values))
	{
	  printf("Not a propositional tautology : ");
	  print_formula(op->definingFormula);
	  printf("\n");
	  return 0;
	}
    }
  return 1;
}

/**
   Test if operands can be freely substituted in def->definingFormula.
   If it can, the forall instance axiom will yield the equivalence
   def->name(operands) <=> subst operands into def->definingFormula

   For example the inclusion relation
   x \subseteq y  ==  \A z : z \in x => z \in y

   The formula x \subseteq z cannot be replaced by \A z : z \in x => z \in z
*/
unsigned char free_define(const struct formula_list* operands,
			  const formula* def)
{
  if (!operands)
    return 1;

  unsigned char capture(const char* v, const struct string_list* boundVars)
  {
    // Search a substitution for variable v
    const struct formula_list* subst = operands;
    const struct formula_list* defOper = def->operands;
    while (subst)
      {
	if (strcmp(v, defOper->formula_elem->name))
	  break;
	subst = subst->next;
	defOper = defOper->next;
      }

    return subst ? variable_capture(subst->formula_elem, boundVars) : 0;
  }

  return !find_variable(def->definingFormula, 0, capture);
}

/**
   Test whether f <=> opDef->definingFormula and if it is,
   clone and substitute variables in opDef->definingFormula.
 */
formula* equivalent_defining_formula(const formula* f,
				     const formula* opDef,
				     const formula_set operatorDefinitions)
{
  if (!f || !free_define(f->operands, opDef))
    return (formula*)0;
  
  if (!f->operands)
    return opDef->definingFormula; // share the formula when there is no substitution of variables

  variable_substitution subs[16];
  variable_substitution* sub = subs;
  struct formula_list* op = f->operands;
  struct formula_list* oop = opDef->operands;
  while (op)
    {
      sub->variable = oop->formula_elem->name;
      sub->subst = op->formula_elem;
      sub++;
      op = op->next;
      oop = oop->next;
    }
  sub->variable = (char*)0;

  formula* def = formula_clone(opDef->definingFormula, subs);

  // Recursively clone the defining formulas
  formula* resolvedF = formula_set_find(def, operatorDefinitions);
  if (resolvedF)
    def->definingFormula = equivalent_defining_formula(def, resolvedF, operatorDefinitions);
  return def;
}

struct formula_list* formula_list_map(const struct formula_list* l,
				      formula* (*func)(const formula* x))
{
  if (l)
    {
      formula* g = func(l->formula_elem);
      return make_formula_list(g, formula_list_map(l->next, func));
    }
  else
    return (struct formula_list*)0;
}

formula* formula_clone(const formula* f, variable_substitution* freeSubs)
{
  if (!f)
    return (formula*)0;
  
  variable_substitution* sub = variable_substitution_find(f->name, freeSubs);
  if (sub && sub->variable)
    return formula_clone(sub->subst, (variable_substitution*)0); // recursive substitutions ?

  formula* c = make_formula(f->builtInOp,
			    f->name ? strdup(f->name) : 0,
			    (struct formula_list*) 0,
			    (const char*) 0,
			    0);

  formula* clone_closure(const formula* x)
  {
    return formula_clone(x, freeSubs);
  }

  c->operands = formula_list_map(f->operands, clone_closure);
  // c->definingFormula = formula_clone(f->definingFormula, freeSubs) ???
  // risk that freeSubs capture variables in f->definingFormula
  return c;
}


/**
   A name in a formula of a FOL file can either be a variable or a custom 
   operator. Find which and link the defining formula when appropriate.
*/
short resolve_operator_or_variable(formula* f,
				   const struct formula_list* primitives,
				   const formula_set operatorDefinitions,
				   const struct string_list* variables,
				   const struct formula_list* opVariables, // should be a union with variables
				   const struct formula_list* proofLocalDecl)
{
  if (!f || (f->builtInOp == lnone && !f->name))
    return 1; // nothing to resolve
  
  unsigned char same_name_as_f(const formula* op)
  {
    // Cannot use formula_compare_operators for variables,
    // because opVariables are typed as variables, but f not yet.
    return f->name && op->name && strcmp(op->name, f->name) == 0;
  }
  unsigned char same_op_as_f(const formula* op)
  {
    // Primitive symbols can either be builtIns, like \in, or named.
    return formula_compare_operators(f, op) == 0;
  }

  // Try variables
  if (string_list_contains(variables, f->name)
      || formula_list_find_const(opVariables, same_name_as_f))
    {
      // TODO search in operators too and report an error
      // if f->name is multiply defined
      f->builtInOp = variable;
      return 1;
    }

  // Try operators
  formula* resolvedF = formula_set_find(f, operatorDefinitions);
  if (!resolvedF)
    {
      const struct formula_list* l = formula_list_find_const(proofLocalDecl, same_op_as_f);
      if (l)
	resolvedF = l->formula_elem;
    }
  if (resolvedF)
    {
      int fOperCount = formula_list_size(f->operands);
      int resFOperCount = formula_list_size(resolvedF->operands);
      if (fOperCount != resFOperCount)
	{
	  printf("%s:%d: bad number of operands for %s ",
		 f->file,
		 f->first_line,
		 f->name ? f->name : op_to_string(f->builtInOp));
	  return 0;
	}
      f->definingFormula = equivalent_defining_formula(f, resolvedF, operatorDefinitions);
      return 1;
    }

  // Try primitive symbols (which have no defining formulas)
  if (formula_list_find_const(primitives, same_op_as_f))
    return 1;

  printf("%s:%d: Unknown name %s\n",
	 f->file,
	 f->first_line,
	 f->name ? f->name : op_to_string(f->builtInOp));
  return 0;
}

/**
   Mark all variables inside f with builtInOp variable.
   Link all operators inside f to their defining formulas.
*/
unsigned char resolve_names(/*out*/formula* f,
			    const struct formula_list* primitives,
			    const formula_set operatorDefinitions,
			    const struct string_list* variables,
			    const struct formula_list* opVariables, // should be a union with variables
			    const struct formula_list* proofLocalDecl)
{
  // TODO refuse nested quantified variables with same name

  // TODO check that operators (\in, +) are declared in CONSTANT clauses

  if (f->builtInOp == forall
      || f->builtInOp == exists
      || f->builtInOp == choose)
    {
      // Only one operand to check
      struct string_list bindVariable;
      bindVariable.string_elem = f->name;
      bindVariable.next = (struct string_list*)variables;
      return resolve_names(f->operands->formula_elem, primitives,
			   operatorDefinitions, &bindVariable,
			   opVariables, proofLocalDecl);
    }
  else
    {
      // resolve operands first, because they can go in f->definingFormula
      unsigned char resolve_error(formula* oper)
      {
	return !resolve_names(oper, primitives,
			      operatorDefinitions, variables,
			      opVariables, proofLocalDecl);
      }
      if (formula_list_find(f->operands, resolve_error))
	return 0;
    }

  if (is_custom_operator(f)
      && !resolve_operator_or_variable(f, primitives, operatorDefinitions,
				       variables, opVariables, proofLocalDecl))
    {
      
      return 0;
    }
  return 1;
}

const formula* get_named_quantifier(enum builtin_operator q, const formula* f, const char* name)
{
  if (f->builtInOp == q
      && strcmp(f->name, name) == 0)
    return get_first_operand(f);
  // assume f <=> f->definingFormula
  if (f->definingFormula
      && f->definingFormula->builtInOp == q
      && strcmp(f->definingFormula->name, name) == 0)
    return get_first_operand(f->definingFormula);
  return 0;
}

short check_quantifier_instance_statement_one(enum reason_kind rk,
					      const formula* f,
					      struct formula_list* subs,
					      const formula_set ops)
{
  if (f->builtInOp != limplies)
    return 0;
  const formula* quant = rk == forallInstance
    ? get_first_operand(f) : get_second_operand(f); // f is a =>, its first operand is a \A
  const formula* instance = rk == forallInstance
    ? get_second_operand(f) : get_first_operand(f);
  
  // Check quant starts with forall quantifiers and fill substitutions
  variable_substitution freeSubst[16];
  variable_substitution* freeSub = freeSubst;
  struct formula_list* sub = subs;
  while (sub)
    {
      quant = get_named_quantifier(rk == forallInstance ? forall : exists,
				   quant, sub->formula_elem->name);
      if (!quant)
	return 0;

      if (sub->next->formula_elem->builtInOp != variable
	  || strcmp(sub->next->formula_elem->name, sub->formula_elem->name) != 0)
	{
	  // do not substitute a variable with itself
	  freeSub->variable = sub->formula_elem->name;
	  freeSub->subst = sub->next->formula_elem;
	  if (!formula_is_term(freeSub->subst, ops))
	    return 0;
	  freeSub++;
	}
      sub = sub->next->next;
    }
  freeSub->variable = (char*)0;

  const short eq = formula_equal(instance,
				 quant,
				 (struct string_list*)0, // no bound variables
				 freeSubst,
				 0);
  return eq;
}

short check_propositional_tautology_statement_one(const formula* statement,
						  const formula* propoTaut,
						  const formula_set ops)
{
  // Propositional tautologies have no quantifiers, so all susbtitutions into them
  // are free. Search for up to 16 such substitutions.

  variable_substitution propositionalVariables[16];
  propositionalVariables[0].variable = (char*)0;
  unsigned char eq = formula_equal(statement, propoTaut,
				   (struct string_list*)0, // no extra bound variables
				   propositionalVariables, 1);
  if (eq)
    {
      // Check all substitutions are propositional (not terms)
      variable_substitution* sub = propositionalVariables;
      while (sub->variable)
	{
	  if (formula_is_term(sub->subst, ops))
	    return 0;
	  sub++;
	}
      return 1;
    }
  return 0;
}

impl_list_type(formula)
impl_set_type(formula, formula_compare_operators)
