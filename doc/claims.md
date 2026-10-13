# What a theorem here claims

Every theorem in Rainbow is checked by the kernel. That tells you the proof is
correct. It does not, by itself, tell you how much the theorem says. This page
explains the two kinds of statement you will meet, and how to see which one you
are looking at.

## For all inputs, or a worked instance

**A statement for all inputs** quantifies over data. For example, from
`math/finite/rational_argmax.clj`:

```
decision/finite-nnrat-argmax-dominates :
  for every type of actions A, every finite set of actions, every scoring
  function, and every candidate in the set:
    score(candidate) <= score(argmax)
```

It holds for every input the types allow, including inputs nobody has tried.

**A worked instance** is a statement about specific values. For example, from
the Christofides module:

```
christofides/tour-at-most-bound :  13 <= 15
```

It is a correct, kernel-checked fact about these numbers: a tour of cost 13 is
within the bound 15 for an instance whose optimum is 10. It says nothing about
other tours, and nothing about the Christofides algorithm's 3/2 approximation
guarantee, which is a classical result not proved here.

Worked instances are still useful. They pin down what an algorithm's decision
step computes on concrete data, they are re-checked on every run, and they catch
a changed definition at once. But they are not general theorems, and Rainbow does
not present them as such.

## How to tell which you have

`lein verify` installs a module through the kernel and classifies every theorem
it names from the theorem's own type:

```sh
lein verify rainbow.algorithms.proofs.ahof.christofides
```

```
OK    rainbow.algorithms.proofs.ahof.christofides (3 theorems: 0 for all inputs, 3 worked instances)
       checked   instance  christofides/tour-at-most-bound  axiom-free
       ...
```

A theorem is classified `for-all` when its statement quantifies over data, that
is, when one of its leading binders ranges over a type outside `Prop` (numbers,
vectors, sets, a type variable). A statement whose only binders are hypotheses,
such as a negation or an implication between closed propositions, is a worked
instance: it is about specific values.

Modules whose theorems are all worked instances say so at the end of their
docstring ("Scope (measured by the kernel)"), and the note is generated from this
classification, so it cannot be more generous than the kernel.

## The operations-research catalogue

Each of the 222 algorithms of the *Applied Higher-Order Functions* catalogue has
kernel-checked theorems about its decision step: the test, selection or update
the algorithm is built around. For some, those theorems hold for all inputs; for
most, they are worked instances. The algorithm's classical guarantees
(optimality, convergence, approximation ratios, coverage) are claimed only where a
theorem states them. The module docstrings say which, and `lein verify` shows it.

## Axioms

Separately from scope, `lein verify` prints each theorem's axioms: the axioms it
depends on, computed by the kernel. The corpus's theorems report `axiom-free`. See
[`trusted-base.md`](trusted-base.md) for what the kernel itself relies on.
