# Proof bundles

A proof bundle is a self-contained record of declarations proved on top of a public
base: which checkpoint and modules to start from, every new declaration with its proof
term, and the claims (aliases, content ids, axiom closures). `lein verify --bundle`
replays it through the kernel alone.

## Making a bundle

There is no `lein` command that makes a bundle; you make one with two library
calls, `rainbow.main/proof-bundle` and `rainbow.main/write-bundle!`, from a REPL
(`lein repl`) or from a script. The bundle holds every declaration that is in your
environment and not in the base, so the steps are: replay the base, install your
proofs on it, name the theorems you claim.

This example bundles the eight theorems of the proof module
`rainbow.math.rational.nnrat.identities` on top of the default checkpoint. Save it
as `make-bundle.clj` in the repository root:

```clojure
(require '[rainbow.main :as main]
         '[rainbow.checkpoint :as checkpoint]
         '[rainbow.math.rational.nnrat.identities :as identities])

(let [loaded (checkpoint/load-checkpoint main/default-checkpoint)
      _ (assert (= :replayed (:status loaded)) (pr-str (:status loaded)))
      base (:environment loaded)                    ; the checkpoint, replayed by the kernel
      env (identities/extend-environment base)      ; the base with the module's proofs installed
      bundle (main/proof-bundle {:checkpoint main/default-checkpoint
                                 :modules []
                                 :base-env base
                                 :env env
                                 :claims (keys (identities/theorem-ids env))
                                 :meta {:made-by "me"}})]
  (main/write-bundle! "identities.edn" bundle)
  (println "wrote identities.edn:" (count (:declarations bundle)) "declarations,"
           (count (:claims bundle)) "claims"))

(shutdown-agents)
```

and run it (the same forms, without `(shutdown-agents)`, work typed into `lein repl`):

```sh
lein run -m clojure.main make-bundle.clj
```

```
wrote identities.edn: 8 declarations, 8 claims
```

The keys of `proof-bundle`:

| key | what it is |
|---|---|
| `:checkpoint` | the checkpoint the base starts from, as a path in this repository; it is recorded in the bundle and replayed by whoever checks it |
| `:modules` | proof modules installed on the checkpoint before your proofs, by namespace name; they become part of the base, not of the bundle |
| `:base-env` | the environment the checkpoint and `:modules` give; `verify --bundle` rebuilds it and must reach the same environment id |
| `:env` | the base with your declarations installed; everything in it that is not in `:base-env` goes into the bundle |
| `:claims` | the aliases you claim; each is recorded with its content id and its axiom closure |
| `:meta` | anything you like (who made it, how); not checked |
| `:reductions` | optional: the kernel reduction budget to record, if your proofs needed a larger one than the default |

For your own proofs, write them as a proof module ([modules.md](modules.md)) and
call its `extend-environment` in place of the one above. `:claims` takes any list
of aliases, such as `'[nnrat/add-zero-right]`; every declaration that is new in
`:env` goes into the bundle, claimed or not. To bundle proofs on top of other
modules, install those on the checkpoint first, pass the result as `:base-env` and
their names as `:modules`.

Check the bundle with the kernel alone, and convert it to the shared encoding
described below (the output is from v1.5.1; the times vary):

```sh
lein verify --bundle identities.edn
lein share-bundle identities.edn identities-shared.edn
lein verify --bundle identities-shared.edn
```

```
$ lein verify --bundle identities.edn
OK    identities.edn  (5.3 s)
       checked   nnrat/add-zero-left  axiom-free
       checked   nnrat/add-zero-right  axiom-free
       checked   nnrat/divide-one-right  axiom-free
       checked   nnrat/multiply-one-left  axiom-free
       checked   nnrat/multiply-one-right  axiom-free
       checked   nnrat/multiply-zero-left  axiom-free
       checked   nnrat/multiply-zero-right  axiom-free
       checked   nnrat/reciprocal-one  axiom-free
$ lein share-bundle identities.edn identities-shared.edn
identities.edn (57,660 bytes) -> identities-shared.edn (11,037 bytes)
$ lein verify --bundle identities-shared.edn
OK    identities-shared.edn  (5.2 s)
       checked   nnrat/add-zero-left  axiom-free
       checked   nnrat/add-zero-right  axiom-free
       checked   nnrat/divide-one-right  axiom-free
       checked   nnrat/multiply-one-left  axiom-free
       checked   nnrat/multiply-one-right  axiom-free
       checked   nnrat/multiply-zero-left  axiom-free
       checked   nnrat/multiply-zero-right  axiom-free
       checked   nnrat/reciprocal-one  axiom-free
```

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

A third form, the binary file (`lein share-bundle --binary`), writes the same shared
bundle with a one-byte tag per node, back references as variable-length integers and
constants as raw 32-byte hashes: c2 is 5,591 bytes (3,623 gzipped). `lein verify
--bundle` reads it like the EDN forms.

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
