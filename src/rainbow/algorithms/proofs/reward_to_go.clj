(ns rainbow.algorithms.proofs.reward-to-go
  "AHoF D47 Reward-to-Go: the future-reward sum used by policy-gradient methods
  to reduce variance (REINFORCE uses the whole-trajectory return as the weight;
  reward-to-go replaces it with only the rewards from step t onward). The
  reward-to-go of a reward suffix is the fold-sum of that suffix:

      reward-to-go rewards = fold add 0 rewards

  and it satisfies the suffix recurrence that makes it computable in one backward
  pass:

      reward-to-go (r :: rest) = r + reward-to-go rest

  This is exact natural-number arithmetic (`algebra/nat-add` folded over the
  list, identity 0). Discounting and the score-function weighting stay an
  executable concern; what is proved here is the reward-to-go fold, its
  one-step suffix recurrence (by reflexivity through the List.rec computation
  rule), and worked suffix totals that reduce by reflexivity.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.reward-to-go`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def list-nat (function/app (function/const* 'data/List [type-level]) nat))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nat head tail))

(defn- reward-to-go [rewards]
  (function/app (function/const* 'reward-to-go/reward-to-go []) rewards))

;; Definitions --------------------------------------------------------------

;; reward-to-go rewards = fold add 0 rewards
(def reward-to-go-spec
  {:name 'reward-to-go/reward-to-go :kind :definition :universes []
   :type (function/arrow list-nat nat)
   :value
   (function/lam
    [['rewards list-nat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nat
     (function/lam [['ignored list-nat]] nat)
     zero
     (function/lam
      [['head nat] ['tail list-nat] ['tail-to-go nat]]
      (add 'head 'tail-to-go))
     'rewards))})

(def definition-specs [reward-to-go-spec])

;; Theorems -----------------------------------------------------------------

;; The suffix recurrence: reward-to-go (r :: rest) = r + reward-to-go rest.
;; This is the one-step backward pass, proved by the List.rec computation rule
;; (reflexivity).
(def suffix-recurrence-spec
  {:name 'reward-to-go/suffix-recurrence :universes []
   :type (function/forall
          [['head nat] ['tail list-nat]]
          (equality nat
                    (reward-to-go (cons-nat 'head 'tail))
                    (add 'head (reward-to-go 'tail))))
   :value (function/lam
           [['head nat] ['tail list-nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (reward-to-go (cons-nat 'head 'tail))))})

;; Worked suffix totals -----------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nat-list [& elements]
  (reduce (fn [tail element]
            (function/app (function/const* 'data/cons [type-level])
                          nat element tail))
          (function/app (function/const* 'data/nil [type-level]) nat)
          (reverse elements)))

;; Full trajectory [3,2,1]: reward-to-go from step 0 is the total return 6.
(def full-return-example-spec
  {:name 'reward-to-go/full-return-example :universes []
   :type (equality nat
                   (reward-to-go (nat-list (data-nat 3) (data-nat 2)
                                           (data-nat 1)))
                   (data-nat 6))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (reward-to-go (nat-list (data-nat 3) (data-nat 2)
                                                (data-nat 1))))})

;; Reward-to-go from step 1 (suffix [2,1]) is 3 -- less than the full return,
;; which is exactly the variance-reducing effect (drops the past reward 3).
(def suffix-return-example-spec
  {:name 'reward-to-go/suffix-return-example :universes []
   :type (equality nat
                   (reward-to-go (nat-list (data-nat 2) (data-nat 1)))
                   (data-nat 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (reward-to-go (nat-list (data-nat 2) (data-nat 1))))})

;; The empty suffix (past the horizon) has zero reward-to-go.
(def empty-return-example-spec
  {:name 'reward-to-go/empty-return-example :universes []
   :type (equality nat (reward-to-go (nat-list)) zero)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (reward-to-go (nat-list)))})

(def theorem-specs
  [suffix-recurrence-spec full-return-example-spec
   suffix-return-example-spec empty-return-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :reward-to-go (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.reward-to-go))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
