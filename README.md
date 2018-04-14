# HilbertProofs

HilbertProofs is made of three parts :
* A language to write formal mathematical proofs, defined as a flex/bison grammar (files fol.l and fol.y). This language expresses first-order predicate calculus and is a lot inspired by TLA+.
* A proof checker that reads the formal proofs and verifies them.
* A collection of proofs, building simple mathematics from the ZFC axioms (in the math folder).

## Predicate calculus

HilbertProofs writes proofs in the first-order logic framework, hence the FOL extension of the proof files. For more information, please read : [First-order logic](https://en.wikipedia.org/wiki/First-order_logic).

Each proof is written in the Hilbert style, which means as a list of cumulative truths. Hilbert-style formal proofs with minimal axioms and inference rules are much (much !) longer than usual proofs written in English. In comparison to programming languages, Hilbert-style formal proofs would be an assembly language, whereas usual English would be a very high-level language like C++ or Java.

While a minimal set of axioms is practical to prove theoretical properties of mathematics (like Gödel's theorems), more axioms and inference rules make the proofs shorter and easier to write. We introduced such redundant inference rules, saying each time how they could be eliminated to go back to the minimal rules (like a macro expansion in the C programming language).

Propositional tautologies are checked by Boolean affectations of propositional variables, rather than arbitrarily chosing a small subset of them as axioms. Then, any propositional tautology can serve as an axiom scheme in the first-order formal proofs. This allows for quicker propositional (ie Boolean) reasoning. See file math/Tautologies.fol.

## A proof example

Here is the first proof of file ZFC.fol, which proves the existence of a set :

```
aSetExists == \E x : x = x

THEOREM aSetExists
PROOF
VARIABLES x;
(\A x : ~(x = x)) => ~(x = x)   BECAUSE \A(x <- x);
~~(x = x) => ~(\A x : ~(x = x))   BECAUSE Contraposition;
x = x   BECAUSE E_SCHEME;
~~(x = x)   BECAUSE IntroNotNot;
~(\A x : ~(x = x))   BECAUSE MODUS_PONENS;
(\E x : x = x)  <=>  ~(\A x : ~(x = x))   BECAUSE Q_SCHEME;
aSetExists   BECAUSE MODUS_PONENS;
QED
```

The first line `aSetExists == \E x : x = x` simply gives the name `aSetExists` to the formula `\E x : x = x`, which states that a set `x` exists (and that it is equal to itself). Then `THEOREM aSetExists` asserts that formula `aSetExists` can be proven : it is a theorem.

Next comes the proof, which is a sequence a statements separated by semicolons `;`. Each statement is proven by the statements before it, so the proof is an accumulation of truths. The last statement is the formula we wanted to prove, here `aSetExists`. `QED` stands for "quod erat demonstrandum", or in English "what was to be demonstrated". It marks the end of the proof.

Each proof statement contains a formula and a reason, separated by the `BECAUSE` keyword. It asserts that its formula is proven by the reason and the previous statements.
* The first reason invoked is `\A(x <- x)`, which is the instantiation of the universal quantifier `\A`. If a formula is true for any set `x`, then it is true when `x` is replaced by any particular value. Here `x` is replaced by itself to drop merely drop the quantifier `\A x` (allowing the use of an equality axiom `E_SCHEME` three statements after).
* The second reason is `Contraposition`. That is a propositional tautology defined in file `math/Tautologies.fol`, which `ZFC.fol` references by the statement `EXTENDS Tautologies` at the beginning. Any propositional tautology can be used as a reason, the checker will then try to match the propositional variables and implicitely use modus ponens with the previous statements. Here `Contraposition(a,b) == (a => b) => (~b => ~a)`, so propositional variable `a` is matched with formula `(\A x : ~(x = x))`, `b` is matched with `~(x = x)` and modus ponens is used with the first statement.
* The third reason is `E_SCHEME`, which regroups several axioms concerning equality. `x = x` is one of those axioms.
* The fourth reason is `MODUS_PONENS`. It searches the previous statements for an implication and its hypothesis. To prove `~(\A x : ~(x = x))`, it finds the implication `~~(x = x) => ~(\A x : ~(x = x))` and its hypothesis `~~(x = x)`.
* The fifth reason is `Q_SCHEME`. It regroups several axioms related to the quantifiers `\A` and `\E`. Here it states the definition of existence with respect to universal.

## Hilbert's epsilon operator

Mathematics have introduced notations that can easily lead to reasoning on non-existing things. The first and most important is the application of functions : `f[x]`. For example, the square root of 4 is 2, which we write `sqrt[4] = 2`.

A common mistake in proofs is reasoning on `sqrt[x]`, where we showed that `x` is a number, but forgot to prove that `x` is non-negative. More advanced possibly non-existing notations include divisions, limits, differentials and integrals. If we calculate with any of those without first proving they exist, we can end up "proving" false formulas.

And even if we are careful and prove that all the symbols we manipulate exist, the functional notation (introduced by Euler in 1734) forces us to clarify formulas such as

```
sqrt[-7] = 42
```

where `sqrt` is a function only defined on non-negative real numbers. There are 4 possibilities :
* Syntactically incorrect. We decide that `sqrt[-7] = 42` is akin to `x+2 =+ 1-`, a formula that makes no sense.
* Provable. We must then produce a proof of `sqrt[-7] = 42`.
* Contrary provable. We must then produce a proof of `sqrt[-7] # 42`.
* Undecidable. We must then prove that both `sqrt[-7] = 42` and `sqrt[-7] # 42` have no proofs. This is the situation of the axiom of choice and the continuum hypothesis in the Zermelo-Fraenkel axioms.

The syntax checker (flex and bison) cannot tell the difference between formulas `sqrt[-7] = 42` and `sqrt[7] = 42`. It doesn't know enough mathematics : it finds them equally good, or equally bad. Since mathematicians want `sqrt[7] = 42` as syntactically correct, we must also accept `sqrt[-7] = 42` as syntactically correct.

To choose between the last 3 possibilities, we can consider the closely-related formula
```
<<-7, 42>> \in sqrt
```
which states that the couple `<<-7, 42>>` is in the graph of the square root function. This new formula is contrary-provable, because -7 is a negative number. Now is this a proof of `sqrt[-7] # 42` ? It could be if we told the proof checker how to eliminate notations, to go back to formulas that surely exist. Here the checker would need to assume, or prove, that
```
sqrt[-7] = 42 <=> <<-7, 42>> \in sqrt
```

This makes sense and solves the question for 42. However, does it tell whether `sqrt[-7] = sqrt[-7]` ? By the same elimination rule, the checker would go through `sqrt[-7] = sqrt[-7] <=> <<-7, sqrt[-7]>> \in sqrt` and conclude negatively, by the same reason that -7 is a negative number. But the equality axiom tells anything equals itself, so we should conclude positively too and contradict ourselves.

Without a clear answer in all cases, we chose the fourth possibility in HilbertProofs : undecidable. `sqrt[-7]` is defined as a new primitive symbol with only one axiom :
```
<<-7, sqrt[-7]>> \in sqrt <=> \E y : <<-7, y>> \in sqrt
```

Since such a `y` does not exist, the only thing this axiom proves about `sqrt[-7]` is that `<<-7, sqrt[-7]>> \notin sqrt`. This tells us absolutely nothing about its equility to 42. The introduction of primitive symbols, subject to existence conditions, is the job of [Hilbert's epsilon operator](https://en.wikipedia.org/wiki/Epsilon_calculus). HilbertProofs makes heavy use of it, calling it CHOOSE. Here is finally the definition of the application of functions :

```
f[x] == CHOOSE y : <<x, y>> \in f
```

The implicit axiom with the existence condition guarantees that nothing wrong can be proven about a CHOOSE object, even when its condition is not satisfied.

## Compile HilbertProofs

Type `make build` to build.

On Windows, you can install MSYS then install flex and bison by typing `pacman -S flex bison` in an MSYS shell.

## Use HilbertProofs

Type `bin/proveMath` to check all the proofs of FOL files in directory `math`.

With emacs it is convenient to execute this command with `M-x compile`, because errors in proofs will highlight in red and be clickable to go to the corresponding lines in the FOL files.

An emacs mode (syntax highlighting, key bindings) for editing FOL files is provided in file fol-mode.el.