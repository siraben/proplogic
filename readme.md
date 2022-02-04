# Exploration of Propositional Logic in Coq

An exploration of propositional logic and propositional calculus in
Coq.  In particular we explore the [soundness and
completeness](https://en.wikipedia.org/wiki/Propositional_calculus#Soundness_and_completeness_of_the_rules)
results of the calculus with respect to the Boolean-valued semantics:

```coq
Theorem l_sound : forall S A, S |- A -> S ⊨ A.
Theorem l_complete : forall S A, S ⊨ A -> S |- A.
```

Currently no classical axioms are used, thus the proofs are fully
constructive.

The repository contains the following files:

- `proplogic.v` - my developments
- `proplogicST.v` - developments due to [Steven Tschantz](https://my.vanderbilt.edu/universalalgebralogic/people/)
- `prop_equiv.v` - equivalence of the developments and examples of
  transporting results between them

A formalization of analogous results for first-order logic is planned.

## Building
```ShellSession
$ make -f CoqMakefile
```
