(ns rainbow.nnrat-farkas-vector-worked-instance-test
  "POSITIVE worked-instance tests for the LP Fourier-Motzkin elimination's
  arithmetic core, nnrat/farkas-cross-vectors.

  The vacuity tests show the round-level theorems assert only that SOME feasible
  reduced system exists (empty included). These tests show the complementary
  fact: the underlying elimination ACTUALLY COMPUTES a specific, correct,
  non-trivial reduced constraint on concrete numbers -- the content the round
  discards by existential quantification.

  Method: instantiate farkas-cross-vectors with concrete nnrat values, supply
  concrete proofs of the two input inequalities (decide-at-most-true-sound with
  a reflexivity witness, valid because the decision procedure computes on
  concrete inputs), and check the resulting reduced-constraint proof against
  (a) the exact expected inequality -- it must be :checked, so the machinery
  computed those exact endpoints -- and (b) the REVERSED inequality -- it must
  be REJECTED, so the reduced constraint is a specific true fact, not something
  vacuously provable. Two instances: one exercises the tail-scaling path
  (eval(scale ..) over a non-empty tail), one the constant-multiply path
  (b_L * u_coeff with u_coeff /= 1).

  A failure here means the elimination arithmetic changed -- farkas-cross-
  vectors no longer reduces the concrete system to the stated constraint.
  Tests only; no proved brick edited, no direction picked."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.kernel :as kernel]
            [rainbow.elaborate :as elaborate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-cross-vectors-list :as cross-vectors-list]
            [rainbow.math.rational.nnrat.order-total :as order-total]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ;; cross-vectors-list transitively extends cross-vectors
          cross-vectors-list/extend-environment
          order-total/extend-environment))))

(def ^:private tl [:succ [:zero]])
(def ^:private R (function/const* 'nnrat/NonnegativeRational []))
(def ^:private zero (function/const* 'nnrat/zero []))
(def ^:private one (function/const* 'nnrat/one []))
(defn- nn-add [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- nn-mul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(def ^:private two (nn-add one one))
(def ^:private three (nn-add two one))
(def ^:private four (nn-add three one))

(def ^:private bool (function/const* 'data/Bool []))
(def ^:private true-value (function/const* 'data/true []))
(def ^:private refl-true
  (function/app (function/const* 'equality/reflexive [tl]) bool true-value))
;; concrete a <= b (valid only when decide a b computes to true)
(defn- decided-at-most [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound []) a b refl-true))

(def ^:private pnn
  (function/app (function/app (function/const* 'data/Product [tl tl]) R) R))
(defn- pair [x y] (function/app (function/const* 'data/pair [tl tl]) R R x y))
(defn- cons-pair [h t] (function/app (function/const* 'data/cons [tl]) pnn h t))
(def ^:private nil-pair (function/app (function/const* 'data/nil [tl]) pnn))
(defn- eval-form [p] (function/app (function/const* 'nnrat/linear-form []) p))
(defn- scale [c p] (function/app (function/const* 'nnrat/farkas-scale-right []) c p))

;; ---- fold-layer builders (one lower against a LIST of uppers) ----
(defn- prod [a b] (function/app (function/const* 'data/Product [tl tl]) a b))
(def ^:private list-pair (function/app (function/const* 'data/List [tl]) pnn))
(def ^:private tail-bound (prod list-pair R))          ; (tail, bound)
(def ^:private uconstraint (prod R tail-bound))        ; (coeff, (tail, bound))
(defn- cons-u [h t] (function/app (function/const* 'data/cons [tl]) uconstraint h t))
(def ^:private nil-u (function/app (function/const* 'data/nil [tl]) uconstraint))
(defn- pair-generic [A B x y] (function/app (function/const* 'data/pair [tl tl]) A B x y))
(defn- mk-upper [coeff tail bound]
  (pair-generic R tail-bound coeff (pair-generic list-pair R tail bound)))
(defn- conjunction [a b] (function/app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b p q] (function/app (function/const* 'proposition/conjoin []) a b p q))
(def ^:private truth (function/const* 'proposition/truth []))
(def ^:private trivial (function/const* 'proposition/trivial []))

;; farkas-cross-vectors applied to a concrete instance; returns the proof term
(defn- cross [x1 l-coeff u-coeff l-tail u-tail b-l b-u]
  (let [lower (decided-at-most b-l (eval-form (cons-pair (pair l-coeff x1) l-tail)))
        upper (decided-at-most (eval-form (cons-pair (pair u-coeff x1) u-tail)) b-u)]
    (function/app (function/const* 'nnrat/farkas-cross-vectors [])
                  x1 l-coeff u-coeff l-tail u-tail b-l b-u lower upper)))

(defn- status [env term type]
  (let [term-e (elaborate/core-expression env term)
        type-e (elaborate/core-expression env type)]
    (cond
      (not= :elaborated (:status term-e)) {:status :term-elab-failed}
      (not= :elaborated (:status type-e)) {:status :type-elab-failed}
      :else (kernel/check env (:term term-e) (:term type-e) #{}))))

(deftest cross-vectors-computes-the-reduced-constraint-tail-scaling
  (testing "instance with non-empty tails (exercises eval(scale ..)):
            lower 0 <= x1 + a2l*x2, upper x1 + a2u*x2 <= 3, at x1=x2=1,
            coeffs 1 -> reduced constraint is exactly at-most 1 4"
    (let [env @checked-environment
          tail (cons-pair (pair one one) nil-pair)     ; coeff 1 on x2=1
          term (cross one one one tail tail zero three)]
      (is (= :checked (:status (status env term (at-most one four))))
          "farkas-cross-vectors should reduce this concrete system to at-most 1 4")
      (is (not= :checked (:status (status env term (at-most four one))))
          "the reduced constraint must be the specific true fact 1<=4, not the false reverse 4<=1"))))

(deftest cross-vectors-computes-the-reduced-constraint-constant-multiply
  (testing "instance with empty tails and u-coeff=2 (exercises b_L*u_coeff):
            lower 1 <= x1, upper 2*x1 <= 3, at x1=1 -> reduced at-most 2 3"
    (let [env @checked-environment
          term (cross one one two nil-pair nil-pair one three)]
      (is (= :checked (:status (status env term (at-most two three))))
          "farkas-cross-vectors should reduce this concrete system to at-most 2 3")
      (is (not= :checked (:status (status env term (at-most three two))))
          "the reduced constraint must be the specific true fact 2<=3, not the false reverse 3<=2"))))

(deftest cross-vectors-fold-computes-the-reduced-conjunction
  (testing "the per-lower fold (farkas-cross-vectors-reduced-holds) over a LIST
            of two uppers: lower 0 <= x1, uppers [x1<=2, x1<=3] at x1=1, all
            coeffs 1, empty tails -> the reduced conditions are exactly the
            conjunction (at-most 0 2) /\\ ((at-most 0 3) /\\ truth). Exercises
            the list-walking on concrete data."
    (let [env @checked-environment
          x1 one, l-coeff one, l-tail nil-pair, b-l zero
          uppers (cons-u (mk-upper one nil-pair two)
                         (cons-u (mk-upper one nil-pair three) nil-u))
          upper-holds-prop (at-most (eval-form (cons-pair (pair one x1) nil-pair)) two)
          upper-holds-prop2 (at-most (eval-form (cons-pair (pair one x1) nil-pair)) three)
          ;; uh : (u0 holds) /\ ((u1 holds) /\ truth)
          uh (conjoin upper-holds-prop (conjunction upper-holds-prop2 truth)
                      (decided-at-most (eval-form (cons-pair (pair one x1) nil-pair)) two)
                      (conjoin upper-holds-prop2 truth
                               (decided-at-most (eval-form (cons-pair (pair one x1) nil-pair)) three)
                               trivial))
          lower (decided-at-most b-l (eval-form (cons-pair (pair l-coeff x1) l-tail)))
          term (function/app (function/const* 'nnrat/farkas-cross-vectors-reduced-holds [])
                             x1 l-coeff l-tail b-l uppers lower uh)
          expected (conjunction (at-most zero two) (conjunction (at-most zero three) truth))
          reversed-first (conjunction (at-most two zero) (conjunction (at-most zero three) truth))]
      (is (= :checked (:status (status env term expected)))
          "the fold should produce exactly (0<=2) /\\ ((0<=3) /\\ truth)")
      (is (not= :checked (:status (status env term reversed-first)))
          "the first reduced constraint must be 0<=2, not the false reverse 2<=0"))))
