(ns rainbow.nnrat-farkas-partition-covering-design-test
  "Falsifiability of the vacuity FIX design (the design notes,
  'Fix design refined').

  The five theorems are vacuous because a conclusion EXISTS (lower,upper),
  lowers-sat /\\ uppers-sat is inhabited by the EMPTY pair. The proposed fix
  keeps the existential (the partition is proof-dependent, so an explicit-output
  rewrite is not available) and adds a COVERING conjunct tying the output to the
  input:  length(l) + length(u) = length(rows).

  A fix you cannot show wrong is worthless -- so this test makes the DESIGN
  falsifiable, the same way the guard tests are. It constructs a concrete
  one-row system and checks the SAME empty witness against both goals:
    - OLD goal (sat only): the empty pair INHABITS it (:checked) -- the vacuity.
    - NEW goal (sat + covering): the empty pair is REJECTED -- because the
      length obligation 0 = length(rows) = 1 has no inhabitant.
  If the covering conjunct did NOT remove the vacuity, the second check would be
  :checked and this test would FAIL. So the design is demonstrably non-vacuous;
  this is the acceptance criterion the eventual strengthened proof must meet.

  This tests the STATEMENT design only (that the strengthened goal is not
  empty-satisfiable), not yet the strengthened theorem's proof (settling that --
  re-deriving farkas-partition-list-necessary with length tracking -- is the
  next brick). Tests only; no proved brick edited, no direction picked."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.kernel :as kernel]
            [rainbow.elaborate :as elaborate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-partition-list :as partition-list]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (partition-list/extend-environment (:environment checkpoint)))))

(def ^:private tl [:succ [:zero]])
(def ^:private R (function/const* 'nnrat/NonnegativeRational []))
(defn- prod [a b] (function/app (function/const* 'data/Product [tl tl]) a b))
(def ^:private p2 (prod R R))
(def ^:private arow (prod R p2))
(def ^:private list-a (function/app (function/const* 'data/List [tl]) arow))
(def ^:private aff-pair (prod list-a list-a))
(def ^:private nil-a (function/app (function/const* 'data/nil [tl]) arow))
(def ^:private bpq (prod R p2))
(def ^:private bsrow (prod R bpq))
(def ^:private zero (function/const* 'nnrat/zero []))
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))

(defn- pairG [A B x y] (function/app (function/const* 'data/pair [tl tl]) A B x y))
(defn- cons-bs [h t] (function/app (function/const* 'data/cons [tl]) bsrow h t))
(def ^:private nil-bs (function/app (function/const* 'data/nil [tl]) bsrow))
(defn- losat [r x] (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied []) r x))
(defn- upsat [r x] (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied []) r x))
(defn- p1 [v] (function/app (function/const* 'product/first [tl tl]) list-a list-a v))
(defn- p2f [v] (function/app (function/const* 'product/second [tl tl]) list-a list-a v))
(defn- conj- [a b] (function/app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b p q] (function/app (function/const* 'proposition/conjoin []) a b p q))
(def ^:private triv (function/const* 'proposition/trivial []))
(defn- pairA [x y] (function/app (function/const* 'data/pair [tl tl]) list-a list-a x y))
(defn- exists [T p] (function/app (function/const* 'proposition/existence [tl]) T p))
(defn- witness [T p v e] (function/app (function/const* 'proposition/witness [tl]) T p v e))
(defn- len-a [l] (function/app (function/const* 'list/length [tl]) arow l))
(defn- len-bs [l] (function/app (function/const* 'list/length [tl]) bsrow l))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- neq [a b] (function/equality tl nat a b))
(defn- refl-nat [a] (function/app (function/const* 'equality/reflexive [tl]) nat a))

;; a concrete one-row both-sides system (all fields zero) and value w = 0
(def ^:private r0 (pairG R bpq zero (pairG R p2 zero (pairG R R zero zero))))
(def ^:private rows (cons-bs r0 nil-bs))
(def ^:private w zero)

(defn- status [env term goal]
  (let [te (elaborate/core-expression env term)
        ge (elaborate/core-expression env goal)]
    (cond (not= :elaborated (:status te)) {:status :term-elab-failed}
          (not= :elaborated (:status ge)) {:status :goal-elab-failed}
          :else (kernel/check env (:term te) (:term ge) #{}))))

(deftest covering-conjunct-removes-the-empty-witness
  (testing "the covering fix (length(l)+length(u)=length(rows)) makes the goal
            reject the empty pair, while the old goal accepts it -- the same
            empty witness flips :checked -> :rejected"
    (let [env @checked-environment
          old-pred (function/lam [['pr aff-pair]] (conj- (losat (p1 'pr) w) (upsat (p2f 'pr) w)))
          old-goal (exists aff-pair old-pred)
          old-empty (witness aff-pair old-pred (pairA nil-a nil-a)
                             (conjoin (losat nil-a w) (upsat nil-a w) triv triv))
          new-pred (function/lam [['pr aff-pair]]
                                 (conj- (conj- (losat (p1 'pr) w) (upsat (p2f 'pr) w))
                                        (neq (nadd (len-a (p1 'pr)) (len-a (p2f 'pr))) (len-bs rows))))
          new-goal (exists aff-pair new-pred)
          new-empty (witness aff-pair new-pred (pairA nil-a nil-a)
                             (conjoin (conj- (losat nil-a w) (upsat nil-a w))
                                      (neq (nadd (len-a nil-a) (len-a nil-a)) (len-bs rows))
                                      (conjoin (losat nil-a w) (upsat nil-a w) triv triv)
                                      (refl-nat nat-zero)))]
      ;; baseline: the un-strengthened goal IS empty-satisfiable (the vacuity)
      (is (= :checked (:status (status env old-empty old-goal)))
          "baseline broke: the un-strengthened goal no longer accepts the empty pair")
      ;; the fix: the covering-strengthened goal REJECTS the empty pair
      (is (not= :checked (:status (status env new-empty new-goal)))
          "the covering conjunct did NOT remove the vacuity -- the empty pair still
           inhabits the strengthened goal. The fix design is wrong: pick a stronger
           relating conjunct."))))
