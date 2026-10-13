(ns rainbow.math.finite.markov-iteration-semigroup
  "Semigroup law for finite exact-rational Markov iteration.

  Iterating a kernel for m+n steps is equivalent to first iterating for n
  steps and then for m more.  The proof is natural-number induction on m; the
  successor case lifts the induction hypothesis through one kernel step using
  pointwise mass congruence.  This is the temporal-composition prerequisite
  for transitive finite-step reachability.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-iteration :as iteration]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- nat-add [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- kernel-iterate [element states kernel steps mass target]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass target))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))

(def kernel-iterate-add-spec
  (let [right-iterate
        (function/lam
         [['state 'S]]
         (kernel-iterate
          'S 'states 'kernel 'right 'mass 'state))
        motive
        (function/lam
         [['left nat]]
         (function/forall
          [['state 'S]]
          (req
           (kernel-iterate
            'S 'states 'kernel (nat-add 'left 'right) 'mass 'state)
           (kernel-iterate
            'S 'states 'kernel 'left right-iterate 'state))))]
    {:name 'markov/nnrat-kernel-iterate-add
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['states (exact-finset-of 'S)]
       ['kernel (function/arrow 'S 'S nnrat)]
       ['mass (function/arrow 'S nnrat)]
       ['left nat] ['right nat]
       ['state 'S]]
      (req
       (kernel-iterate
        'S 'states 'kernel (nat-add 'left 'right) 'mass 'state)
       (kernel-iterate
        'S 'states 'kernel 'left
        (function/lam
         [['middle 'S]]
         (kernel-iterate
          'S 'states 'kernel 'right 'mass 'middle))
        'state)))
     :value
     (function/lam
      [['S type-u]
       ['states (exact-finset-of 'S)]
       ['kernel (function/arrow 'S 'S nnrat)]
       ['mass (function/arrow 'S nnrat)]
       ['left nat] ['right nat]
       ['state 'S]]
      (app
       (app
        (function/const* 'data/Nat.rec [zero-level])
        motive
        (function/lam
         [['target 'S]]
         (equivalent-reflexive
          (kernel-iterate
           'S 'states 'kernel 'right 'mass 'target)))
        (function/lam
         [['previous nat]
          ['induction-hypothesis (app motive 'previous)]]
         (function/lam
          [['target 'S]]
          (app
           (function/const*
            'markov/nnrat-kernel-step-respects-mass-equivalence [U])
           'S 'states 'kernel
           (function/lam
            [['middle 'S]]
            (kernel-iterate
             'S 'states 'kernel
             (nat-add 'previous 'right) 'mass 'middle))
           (function/lam
            [['middle 'S]]
            (kernel-iterate
             'S 'states 'kernel 'previous right-iterate 'middle))
           'induction-hypothesis 'target)))
        'left)
       'state))}))

(def definition-specs [])
(def theorem-specs [kernel-iterate-add-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-iteration])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-iteration-semigroup theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-iteration-semigroup))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
