# A tour of the repository

Six stops, from the part you must trust to a theorem you would put on a slide.
Each stop names a file you can open and a command you can run. Commands are run
from the repository root.

## 1. The kernel — what you have to trust

`src/rainbow/kernel.clj` (915 lines), with `term.clj`, `environment.clj` and
`canonical.clj`: 1,200 lines in all. The functions that matter:

| function | what it does |
|---|---|
| `infer`, `check` | type inference and checking for the dependent calculus |
| `normalize`, `definitionally-equal?` | reduction and the conversion check |
| `add-declaration` | the only way a declaration enters an environment: it is checked first |
| `add-inductive-block` | inductive types and their recursors |
| `axioms` | the axioms a declaration depends on, transitively |

Everything else in the repository — elaboration, tactics, proof search,
checkpoint loading — produces terms and hands them to `add-declaration`. A bug
there gives a rejected term, not an accepted false one.
[`trusted-base.md`](trusted-base.md) lists what the kernel itself relies on.

## 2. A small theorem — `nnrat/add-zero-right`

`src/rainbow/math/rational/nnrat/identities.clj`. Non-negative rationals are
pairs, so `x + 0` equals `x` only up to cross-multiplication equivalence, and
the proof says exactly that:

```clojure
(def add-zero-right-spec
  {:name 'nnrat/add-zero-right
   :universes []
   :type
   (function/forall [['value nnrat]]
                    (equivalent (add 'value nnrat-zero) 'value))
   :value
   (function/lam
    [['value nnrat]]
    (let [n (numerator 'value)
          d (denominator 'value)
          ...
```

The `:type` is the statement, the `:value` is the proof term, and both are
ordinary Clojure data built by small helper functions. The module's
`theorem-specs` lists eight such laws, and its `extend-environment` installs them
through the kernel.

```sh
lein verify rainbow.math.rational.nnrat.identities
```

## 3. A tactic — the ring normaliser

`src/rainbow/math/rational/nnrat/ring.clj`. Writing every reassociation by hand
does not scale, so `prove-equiv` takes two expressions over `nnrat/add` and
`nnrat/multiply`, normalises both to monomial multisets and, when they agree,
*builds a proof term* chaining the associativity, commutativity and
distributivity laws. If the two sides differ it throws instead.

The tactic is not trusted: what it returns is a term like any other, and the
kernel checks it. `src/rainbow/math/nat/ring.clj` is the same idea over the
natural numbers.

## 4. An algorithm guarantee — finite argmax

`src/rainbow/math/finite/rational_argmax.clj`. An argmax over a finite set of
actions, with a theorem that holds for every input:

```clojure
{:name 'decision/finite-nnrat-argmax-dominates
 :universes ['u]
 :type
 (function/forall
  [['A type-u] ['actions (exact-finset-of 'A)]
   ['initial 'A] ['score (function/arrow 'A nnrat)]
   ['candidate 'A]
   ['candidate-member (source-membership 'A 'actions 'candidate)]]
  (rational-at-most (function/app 'score 'candidate)
                    (function/app 'score result)))
 ...}
```

For any type of actions, any finite set of them and any scoring function, the
action argmax returns scores at least as high as every member. Maximum expected
utility, Borda counting, the Vickrey auction and the argmin dual in the corpus
reuse it. The 222-algorithm catalogue lives in `src/rainbow/algorithms/proofs/`,
next to the reference implementations they are about in
`src/rainbow/algorithms/reference/`.

```sh
lein verify rainbow.math.finite.rational-argmax
```

## 5. A milestone — how the corpus was built

`src/rainbow/milestones/ahof_bisection.clj`. Each result was added by a
milestone driver with a fixed shape: a precommitted target list
(`precommit.edn`), a `run` function that starts from an input checkpoint, proves
the targets and returns a new checkpoint and a report, and a recorded output in
`artifacts/`. The checkpoint is named by the hash of its content, so

```sh
lein reproduce rainbow.milestones.ahof-bisection
```

rebuilds it from source and tells you whether you got the same hash. `run`
writes nothing; the recorded evidence is only read.

## 6. A real theorem — the finite ergodic theorem

`src/rainbow/math/finite/markov_ergodic_uniqueness.clj` and its neighbours. For a
finite Markov kernel whose Dobrushin coefficient is certified below one, any two
stationary distributions of equal mass agree at every state:

```
markov/nnrat-stationary-pointwise-unique-of-dobrushin-bound
```

The proof composes a contraction bound (`markov_dobrushin_contraction.clj`) with
a conditional uniqueness theorem (`markov_contraction_uniqueness.clj`); geometric
decay and the Metropolis-Hastings instantiation are next to it
(`markov_geometric_decay.clj`, `index_hastings_ergodic.clj`). It is native and
axiom-free, which `lein verify` will show you.

```sh
lein verify rainbow.math.finite.markov-ergodic-uniqueness
```

## Where to go next

- [`corpus.md`](corpus.md): every proof module, by topic, with its one-line
  description.
- [`maturity-levels.md`](maturity-levels.md): what a result does and does not
  claim.
- `src/rainbow/history/`: how the prover grew, from the first direct-term corpus
  (`direct_term_corpus.clj`) and the first tactic program (`first_tactic_program.clj`)
  to the Lean round trip (`lean_round_trip.clj`).
