# HilbertProofs

HilbertProofs is made of three parts :
* A language to write formal mathematical proofs, defined as a flex/bison grammar (files fol.l and fol.y). This language expresses first-order predicate calculus and is inspired by TLA+.
* A proof checker that reads the formal proofs and verifies them.
* A collection of proofs, building simple mathematics from the ZFC axioms (in the math folder).

## First-order predicate calculus in the Hilbert style

HilbertProofs writes proofs in the first-order logic framework with equality, hence the FOL extension of the proof files. For more information, please read : [First-order logic](https://en.wikipedia.org/wiki/First-order_logic).

Each proof is written in the [Hilbert style](https://en.wikipedia.org/wiki/Hilbert_system), which means as a list of cumulative truths. This is different from [natural deduction](https://en.wikipedia.org/wiki/Natural_deduction), where the proofs are structured more like a tree of formulas.

HilbertProofs' detailed inference rules are given another section below.

## Can we trust HilbertProofs ?

HilbertProofs' sole purpose is to increase the confidence we have in mathematical proofs. To this end, the proofs in its formal language are a lot more tedious to write than in usual mathematical English. Is is worth the effort ?

Firstly, the rigidity and simplicity of HilbertProofs' language make all proofs' statements absolutely clear. Abuse of notations and shortcuts by ambiguous sentences are impossible, by lack of grammar. In contrast, we can think of the many questions posted on the Internet, concerning whether the axiom of choice was used in a particular proof. In HilbertProofs there is no doubt : an axiom is used when a proof statement ends with "BECAUSE AXIOM". English also permits to be lazy, by saying only that a function is continuous, or that an object is a group. But for which topologies ? Which operations ? HilbertProofs' syntax forces us to make all parts of a structure explicit, every time we claim an object has it.

Secondly, if one does not want to check the formal proofs themselves, HilbertProofs provides an automated checker. This is again possible thanks to the simplicity of the formal proof language. At the moment, there are about 9000 lines of C code in HilbertProofs, 5000 of which coming from the flex/bison transformation of the grammar. Then we have the millions of lines in the source code of GCC, the C compiler HilbertProofs uses. The correctness of the automated checker is the correctness of all those lines of code, the absence of bugs in them.

GCC and bison have been used and tested for 30 years, the risk of bugs in them is fairly small. If one does not trust them, one has the option to read and debug the assembly they produce, which is 45000 lines for HilbertProofs, including the debugging symbols. The remaining 4000 lines of HilbertProofs were tested by careful code reviews, which are possible given their small size. They are also tested by the 7000 lines in the FOL files, that prove basic theorems of mathematics we know are true. In the process of writing those 7000 lines, the automated checker found lots of errors. Finally, debugging HilbertProofs benefits all its proofs ; whereas correcting an English proof only benefits that particular proof.


## ASCII notations of formulas

For compatibility with most editors and tools, the charset of HilbertProofs is ASCII. Here is how logical connectors are written
* `~a` means not a
* `a \/ b` means a or b
* `a /\ b` means a and b
* `a => b` means a implies b
* `a <=> b` means a equivalent to b
* `\A x : a` means for all x then a
* `\E x : a` means there exists an x such that a

Subformulas can be enclosed with parentheses `(` and `)`, otherwise the precedence rules make those two formulas equal :
```
~a /\ b => c \/ d
((~a) /\ b) => (c \/ d)
```

## A proof example

Here is a proof in file ZFC.fol, which proves the existence of a set :

```
aSetExists == \E x : x = x

THEOREM aSetExists
PROOF
VARIABLES x;
(\A x : ~(x = x)) => ~(x = x)   BECAUSE \A(x <- x);
~~(x = x) => ~(\A x : ~(x = x))   BECAUSE Contraposition;
equalSelf   BECAUSE THEOREM;
x = x   BECAUSE \A(a <- x);
~~(x = x)   BECAUSE IntroNotNot;
~(\A x : ~(x = x))   BECAUSE MODUS_PONENS;
(\E x : x = x)  <=>  ~(\A x : ~(x = x))   BECAUSE Q_SCHEME;
aSetExists   BECAUSE MODUS_PONENS;
QED
```

The first line `aSetExists == \E x : x = x` simply gives the name `aSetExists` to the formula `\E x : x = x`, which states that a set `x` exists (and that it is equal to itself). Then `THEOREM aSetExists` asserts that formula `aSetExists` can be proven : it is a theorem.

Next comes the proof, which is a sequence a statements separated by semicolons `;`. Each statement is proven by the statements before it, so the proof is an accumulation of truths. The last statement is the formula we wanted to prove, here `aSetExists`. `QED` stands for "quod erat demonstrandum", or in English "what was to be demonstrated". It marks the end of the proof.

Each proof statement contains a formula and a reason, separated by the `BECAUSE` keyword. It asserts that its formula is proven by the reason and the previous statements.
* The first reason invoked is `\A(x <- x)`, which is the instantiation of the universal quantifier `\A`. If a formula is true for any set `x`, then it is true when `x` is replaced by any particular value. Here `x` is replaced by itself to merely drop the quantifier `\A x` (allowing the use of the theorem `equalSelf` three statements after).
* The second reason is `Contraposition`. That is a propositional tautology defined in file `math/Tautologies.fol`, which `ZFC.fol` references by the statement `EXTENDS Tautologies` at the beginning. Any propositional tautology can be used as a reason, the checker will then try to match the propositional variables and implicitely use modus ponens with the previous statements. Here `Contraposition(a,b) == (a => b) => (~b => ~a)`, so propositional variable `a` is matched with formula `(\A x : ~(x = x))`, `b` is matched with `~(x = x)` and modus ponens is used with the first statement.
* The third reason is `THEOREM`, which invokes a previously proven theorem, here `equalSelf`.
* The fourth reason is `MODUS_PONENS`. It searches the previous statements for an implication and its hypothesis. To prove `~(\A x : ~(x = x))`, it finds the implication `~~(x = x) => ~(\A x : ~(x = x))` and its hypothesis `~~(x = x)`.
* The fifth reason is `Q_SCHEME`. It regroups several axioms related to the quantifiers `\A` and `\E`. Here it states the definition of existence with respect to universal.

## Inference rules

Here are the inference rules hardcoded in the C layer of HilbertProofs. Those are not redefinable or modifiable in the FOL files. `x,y,z` are any variables and `p,q` any formulas. Under `E_SCHEME`,
* `x = y /\ x = z => y = z`
* `x = y => y = x`
* `\A x1 : \A y1 : ... : \A xK : \A yK : (x1 = y1 /\ ... /\ xK = yK) => (s <=> s(x1 <- y1, ..., xK <- yK))` where `xJ <- yJ` are renaming of free variables. HilbertProofs checks that the xJ's and yJ's are distinct and that formula `s` doesn't have free variables in the yJ's. For example, this is a valid E_SCHEME statement, `\A x : \A y : x = y => (x \in a <=> y \in a)`.

Under `Q_SCHEME`,
* `(\A x : p => q)  =>  ( (\E x : p) => (\E x : q) )`
* `(\A x : p => q)  =>  ( (\A x : p) => (\A x : q) )`
* `(\E x : p) <=> ~(\A x : ~p)`
* `(\A x : p => q) => (p => \A x : q)` when varibale x has no free occurrences in p
* `(\E x : p => q) => (p => \E x : q)` when varibale x has no free occurrences in p
* `(\E x : p) => p` when varibale x has no free occurrences in p

And finally we have the instances of quantifiers
* `(\A x : p) => p(x <- t)`
* `p(x <- t) => \E x : p`
where `p(x <- t)` means the free substitution of variable `x` by term `t`. HilbertProofs checks that all variables of `t` remain free in `p(x <- t)`.

The truth tables used in the checking of propositional tautologies are also hardcoded. For example, the truth table of implication is `(0 => 0) = 1, (0 => 1) = 1, (1 => 0) = 0, (1 => 1) = 1`.

Propositional tautologies are checked by Boolean affectations of propositional variables, rather than by arbitrarily chosing a small subset of them as axioms. Then, any propositional tautology can serve as an axiom scheme in the first-order formal proofs. This allows for quicker propositional (ie Boolean) reasoning. See file math/Tautologies.fol.

## Conservative extensions, aka definitions

The ZFC theory, which builds all mathematics, can be expressed with only one primitive symbol : the binary relation of membership `\in`. However if we only use this symbol, simple formulas like `a \subseteq (b \union c)`, which states that a set `a` is included in the union of sets `b` and `c`, explode as
```
\E u : (\A x : x \in u <=> (x \in b \/ x \in c)) /\ (\A z : z \in a => z \in u)
```

While this is easy for a computer to parse and check, it is unreadable for a human. It forces us to copy and paste the definition of subset, union, intersection, powerset and all other operations of set theory every time we use them. Fortunately, predicate calculus is quite flexible and lets us introduce new primitive symbols, along with axioms to use them. Recall that predicate calculus was first used by Euclid to formalize geometry : he introduced symbols like "point" and "line" instead of a membership relation `\in`. So, to define the subset relation in HilbertProofs we can write
```
CONSTANT _ \subseteq _
AXIOM \A x : \A y : x \subseteq y <=> \A z : z \in x => z \in y
```

However, each time we add an axiom we must think : does it break the theory ? Does it introduce contradictions ? Does it prove or disprove previously undecidable formulas ? There are cases like the one above where we are sure that the new axiom does not affect the formulas of the previous theory : [conservative extensions](https://en.wikipedia.org/wiki/Conservative_extension). Roughly speaking, when the new axiom concerns only the new primitive symbol (`\subseteq` above), then it does not affect formulas that do not use the new symbol. Precisely speaking, each [model](https://en.wikipedia.org/wiki/Model_theory) of the previous theory can be extended to a model of the new theory, so by [Gödel's completeness theorem](https://en.wikipedia.org/wiki/G%C3%B6del%27s_completeness_theorem) there are no more contradictions.

HilbertProofs has 3 syntactic constructs which guarantee that an axiom is a conservative extension, via a new primitive symbol. The subset relation is defined by the first of these constructs :
```
x \subseteq y == \A z : z \in x => z \in y
```

The proof checker implicitly unfolds this statement as the `CONSTANT/AXIOM` above, but when you write it as `==` you are sure the axiom is conservative. The second conservative construct lets us define symbols of operators from previously defined operators, like
```
x \union y == UNION { x, y }
```
where [UNION](https://en.wikipedia.org/wiki/Union_(set_theory)#Arbitrary_unions) is the general union of a set, and `{ x, y }` is the [unordered pair](https://en.wikipedia.org/wiki/Unordered_pair) of `x` and `y`. The checker unfolds this construct to
```
CONSTANT _ \union _
AXIOM \A x : \A y : x \union y = UNION { x, y }
```

The last conservative construct lets us define the symbol of an operator by a property we want it to have, when possible. For example the operator that applies a function `f` to an argument `x` :
```
f[x] == CHOOSE y : <<x, y>> \in f
```

`<<x,y>>` is the [couple](https://en.wikipedia.org/wiki/Tuple) which first element is `x` and second element `y`. So the image of `x` by function `f` is an element `y` coupled to `x` in the graph of `f`. But what if such a `y` does not exist, as in `sqrt[-7]`, the non-existent square root of -7 ? `== CHOOSE` is unfolded like this :

```
CONSTANT _ [ _ ]
AXIOM \A f : \A x : (\E y : <<x,y>> \in f) => <<x,f[x]>> \in f
```

This axiom lets us say nothing about `f[x]` until we have proven `(\E y : <<x,y>> \in f)`, which means that `f[x]` exists. The `== CHOOSE` construct can be used in HilbertProofs to define, among others, the application of a function `f[x]`, the division of numbers `a/b`, the differential of a function `f'` and the integral of a function. It protects our proofs from applying functions where they're not defined, dividing by zero, differentiating a function that is not differentiable, or integrating a function that is not integrable.

## Recursive definitions

Recall that the factorial of a natural number n is the product of all numbers up to n, so this could be its definition
```
Factorial(n) == CHOOSE p : (n = 1 /\ p = 1) \/ (n # 1 /\ p = n * Factorial(n-1))
```
This looks like a recursive definition, because `Factorial` is on both sides of the `==`. But remember that it is only syntactic sugar to write a `CONSTANT/AXIOM` pair, as well as ensuring it is a conservative extension of the theory. In predicate calculus, the definition of a symbol is only its name and arity, so here
```
CONSTANT Factorial( _ )
```
Then the symbol may appear in one or more axioms, so that the theory can prove formulas involving the symbol. Here,
```
AXIOM \A n : (\E p : (n = 1 /\ p = 1) \/ (n # 1 /\ p = n * Factorial(n-1)))
   => ((n = 1 /\ Factorial(n) = 1) \/ (n # 1 /\ Factorial(n) = n * Factorial(n-1)))
```

`Factorial` has several occurrences in this axiom, and that is perfectly fine. The recursion of the previous definition was only an illusion caused by the `==` syntactic construct.

However, it is much harder to prove that this axiom is a conservative extension. As explained above, the proof that a new symbol and its axiom are conservative is by model extension. So for `newOp(n) == CHOOSE x : P`, we extend a model M of the previous theory by taking for `newOp(n)`,
* when M satisfies `\E x : P`, any such `x`
* otherwise, any element of the domain of M

But this reasoning only holds when formula `P` doesn't involve `newOp`. If `P` involves `newOp` as `Factorial` does, then it is not a formula in the language of the previous theory : knowing whether M satisfies `\E x : P` makes no sense.

For this reason, the parser forces all symbols on the right-hand side of a `==` to be defined before the `==`. If this refuses the definition of one of your symbols like `Factorial`, you must write the `CONSTANT/AXIOM` pair explicitly. And you have to prove yourself that your axiom is conservative. HilbertProofs won't help you there, it has no syntax to quantify formulas or express that a theory is a conservative extension of another. Even less a checker for proofs that those extensions are conservative.

In the case of `Factorial`, we can easily stay in the framework of HilbertProofs by making it a function (0-ary symbol), rather than a unary symbol :
```
Factorial == CHOOSE f : IsFunction(f) /\ Domain(f) = Nat \ {0} /\ f[1] = 1
   /\ (\A n : n \in Nat /\ n > 1 => f[n] = n * f[n-1])
```

## Compile HilbertProofs

The build system of HilbertProofs is a simple makefile ; on Linux or MacOS, type `make build` to build.

On Windows, you can install the build tools [MSYS](https://www.msys2.org/), then use them to get flex and bison by typing `pacman -S flex bison` in an MSYS shell. After that, it is `make build` too in an MSYS shell.

## Use HilbertProofs

Type `bin/proveMath` to check all the proofs of FOL files in directory `math`.

With emacs it is convenient to execute this command with `M-x compile`, because errors in proofs will highlight in red and be clickable to go to the corresponding lines in the FOL files.

An emacs mode (syntax highlighting, key bindings) for editing FOL files is provided in file fol-mode.el.