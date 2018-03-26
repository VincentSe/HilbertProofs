# HilbertProofs

HilbertProofs is made of three parts :
* A language to write formal mathematical proofs, defined as a flex/bison grammar (files fol.l and fol.y). This language is a lot inspired by TLA+.
* A proof checker that reads the formal proofs and verifies them.
* A collection of proofs, building simple mathematics from the ZFC axioms (in the math folder).

Each proof is written in the Hilbert style, which means as a list of cumulative truths. Hilbert-style formal proofs with minimal axioms and inference rules are much (much !) longer than usual proofs written in English. In comparison to programming languages, Hilbert-style formal proofs would be an assembly language, whereas usual English would be a very high-level language like C++ or Java.

 While a minimal set of axioms is practical to prove theoretical properties of mathematics (like Gödel's theorems), more axioms and inference rules make the proofs shorter and easier to write. We introduced such redundant inference rules, saying each time how they could be eliminated to go back to the minimal rules (like a macro expansion in the C programming language).

Propositional tautologies are checked by Boolean affectations of propositional variables, rather than arbitrarily chosing a small subset of them as axioms. Then, any propositional tautology can serve as an axiom scheme in the first-order formal proofs. This allows for quicker propositional (ie Boolean) reasoning.

`make build` to build, then `bin/proveMath` will check the proofs of file `math/zfc.fol`.