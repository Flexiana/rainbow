# Proof bundles

A proof bundle is a self-contained record of declarations proved on top of a public
base: which checkpoint and modules to start from, every new declaration with its proof
term, and the claims (aliases, content ids, axiom closures). `lein verify --bundle`
replays it through the kernel alone.

## Two encodings of the same declarations

| | plain (schema 1, 2) | shared (schema 3) |
|---|---|---|
| terms | written as trees | every distinct subterm written once |
| constants | full `sha256:...` id at every reference | a table; references by position |
| c2 trailer-allocation certificate | 2,363,278 bytes | 15,571 bytes |

Proof terms repeat themselves. The RH2EDIN c2 LP certificate's proof has 46,325 term
nodes but only 617 distinct ones, and it names 26 constants 21,938 times; as a tree,
three quarters of the file is the same 71-character hashes. The shared encoding writes
each distinct subterm once, children by position, and each constant once.

What does not change: the terms, the kernel, the claims. Decoding rebuilds exactly the
plain bundle's declarations, so the kernel checks the same terms and computes the same
content ids. `lein share-bundle in.edn out.edn` converts a plain bundle; `--plain`
converts back.

Nothing in the encoding is trusted. The decoder refuses anything malformed (a child
that is not an earlier node, a constant out of range, an unknown tag), and what it
produces still goes through `kernel/add-declaration`, which recomputes every
declaration's id from its content. A decoding defect therefore shows up as a refused
bundle, never as an accepted wrong one; a bundle with one price changed is rejected by
the kernel with its own reason.

## Reading a statement

`lein show <alias> [module ...]` prints a theorem's statement for people:

```
optimization/signed-lp-optimality-certificate-on.{u} :
  (A B : Type u) (M : A → B → ℚ) (b : A → ℚ) (c x : B → ℚ) (y : A → ℚ) (rows : List A)
  (cols : List B)
  (primal-feasible : ∀ i ∈ rows, Σ j∈cols, M i j · x j ≤ b i)
  (dual-feasible : ∀ j ∈ cols, c j ≤ Σ i∈rows, M i j · y i)
  (x-nonnegative : ∀ i ∈ cols, 0 ≤ x i)
  (y-nonnegative : ∀ i ∈ rows, 0 ≤ y i)
  (gap : Σ i∈rows, b i · y i = Σ j∈cols, c j · x j)
  (candidate : B → ℚ)
  (candidate-feasible : ∀ i ∈ rows, Σ j∈cols, M i j · candidate j ≤ b i)
  (candidate-nonnegative : ∀ i ∈ cols, 0 ≤ candidate i)
  → Σ j∈cols, c j · candidate j ≤ Σ j∈cols, c j · x j
```

This is a view. The kernel checks the term, which has no names (binders are de Bruijn
indices) and spells every constant by content id. Binder names come from the theorem's
source spec only when elaborating that spec gives exactly the kernel's type; otherwise
they are generated. Every notation is listed in a legend under the statement with the
constant it stands for (for example, `=` above is `signed/equivalent`, equality of
rational values), and anything cut by the size budget is an explicit `…⟨n⟩` counting
the nodes left out.
