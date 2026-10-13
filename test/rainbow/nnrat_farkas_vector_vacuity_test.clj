(ns rainbow.nnrat-farkas-vector-vacuity-test
  "NEGATIVE tests: living signals for the five provably-vacuous LP
  Fourier-Motzkin theorems documented in the design notes.

  Each theorem below is empty-satisfiable: a TRIVIAL inhabitant (the empty pair
  of lists, or the identity function) inhabits its stated type, so the theorem
  asserts less than its name claims and its ordinary gate cannot fail on the
  substance. These tests construct that trivial inhabitant and assert the
  kernel accepts it (`:checked`).

  READ THIS BEFORE REACTING TO A FAILURE. A PASS means the theorem is STILL
  vacuous -- the defect is present. A FAILURE is GOOD NEWS: it means the
  theorem's type was STRENGTHENED so the trivial inhabitant no longer type-
  checks. When one of these fails, the deftest name tells you exactly which of
  the five was closed -- update the design notes (strike that
  entry) and the design notes, and consider replacing this negative test
  with a positive one for the strengthened statement.

  Method asymmetry (the report's load-bearing sentence): exhibiting a trivial
  inhabitant PROVES vacuity, while failing to find one is strong evidence and
  not a proof of substantiveness. These tests encode the PROVED half.

  Not a proof rewrite: this file adds tests only; it edits none of the five
  theorems (including the pre-existing, shared
  nnrat/farkas-partition-list-necessary) and picks no proof direction."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.elaborate :as elaborate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-vector-step :as vector-step]
            [rainbow.math.rational.nnrat.farkas-partition-list :as partition-list]
            [rainbow.math.rational.nnrat.farkas-eliminate-base :as eliminate-base]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector-step/extend-environment
          partition-list/extend-environment
          ;; eliminate-base is a SUBSTANTIVE theorem, loaded only as the
          ;; control below (it is not otherwise in this chain).
          eliminate-base/extend-environment))))

;; ---- surface term builders (unelaborated; consts are placeholders) ----
(def ^:private tl [:succ [:zero]])
(defn- prod [a b] (function/app (function/const* 'data/Product [tl tl]) a b))
(def ^:private R (function/const* 'nnrat/NonnegativeRational []))
(def ^:private p2 (prod R R))
(def ^:private arow (prod R p2))
(def ^:private list-a (function/app (function/const* 'data/List [tl]) arow))
(def ^:private aff-pair (prod list-a list-a))
(def ^:private nil-a (function/app (function/const* 'data/nil [tl]) arow))
(def ^:private pnn (prod R R))
(def ^:private lpp (function/app (function/const* 'data/List [tl]) pnn))
(def ^:private nvc (prod R (prod R (prod R lpp))))
(def ^:private list-nvc (function/app (function/const* 'data/List [tl]) nvc))
(def ^:private nvc-pair (prod list-nvc list-nvc))
(def ^:private nil-nvc (function/app (function/const* 'data/nil [tl]) nvc))
(def ^:private bpq (prod R p2))
(def ^:private bsrow (prod R bpq))
(def ^:private list-bs (function/app (function/const* 'data/List [tl]) bsrow))
(def ^:private one (function/const* 'nnrat/one []))
(def ^:private nat (function/const* 'data/Nat []))

(defn- losat [r x] (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied []) r x))
(defn- upsat [r x] (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied []) r x))
(defn- lohold [c x] (function/app (function/const* 'nnrat/farkas-cross-vectors-lowers-hold []) c x))
(defn- uphold [c x] (function/app (function/const* 'nnrat/farkas-cross-vectors-uppers-hold []) c x))
(defn- map-uppers [l x] (function/app (function/const* 'nnrat/farkas-adapter-map-uppers []) l x))
(defn- feasible [k] (function/app (function/const* 'nnrat/farkas-vector-feasible []) k))
(defn- succ [k] (function/app (function/const* 'data/succ []) k))
(defn- p1a [v] (function/app (function/const* 'product/first [tl tl]) list-a list-a v))
(defn- p2a [v] (function/app (function/const* 'product/second [tl tl]) list-a list-a v))
(defn- p1n [v] (function/app (function/const* 'product/first [tl tl]) list-nvc list-nvc v))
(defn- p2n [v] (function/app (function/const* 'product/second [tl tl]) list-nvc list-nvc v))
(defn- conj- [a b] (function/app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b p q] (function/app (function/const* 'proposition/conjoin []) a b p q))
(def ^:private triv (function/const* 'proposition/trivial []))
(defn- pairA [x y] (function/app (function/const* 'data/pair [tl tl]) list-a list-a x y))
(defn- pairN [x y] (function/app (function/const* 'data/pair [tl tl]) list-nvc list-nvc x y))
(defn- witness [T pred v ev] (function/app (function/const* 'proposition/witness [tl]) T pred v ev))
(defn- reduced-conditions [rows w] (function/app (function/const* 'nnrat/farkas-reduced-conditions []) rows w))
(defn- lower-input-hold [l x2 x1] (lohold (map-uppers l x2) x1))
(defn- upper-input-hold [l x2 x1] (uphold (map-uppers l x2) x1))
;; builders for the substantive CONTROL (farkas-eliminate-base)
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- nn-add [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- eval-form [pairs] (function/app (function/const* 'nnrat/linear-form []) pairs))
(def ^:private nil-pair (function/app (function/const* 'data/nil [tl]) pnn))

;; ---- the five trivial inhabitants ----
(defn- round-witness []
  (let [goal-pred (fn [x] (function/lam [['pr aff-pair]]
                                        (conj- (losat (p1a 'pr) x) (upsat (p2a 'pr) x))))]
    (function/lam [['lowers list-nvc] ['uppers list-nvc] ['x1 R] ['x2 R]
                   ['lh (lower-input-hold 'lowers 'x2 'x1)]
                   ['uh (upper-input-hold 'uppers 'x2 'x1)]]
                  (witness aff-pair (goal-pred 'x2) (pairA nil-a nil-a)
                           (conjoin (losat nil-a 'x2) (upsat nil-a 'x2) triv triv)))))

(defn- step-witness []
  (let [held-pred (fn [x] (function/lam [['pr nvc-pair]]
                                        (conj- (lohold (map-uppers (p1n 'pr) one) x)
                                               (uphold (map-uppers (p2n 'pr) one) x))))]
    (function/lam [['lowers list-nvc] ['uppers list-nvc] ['x1 R] ['x2 R]
                   ['lh (lower-input-hold 'lowers 'x2 'x1)]
                   ['uh (upper-input-hold 'uppers 'x2 'x1)]]
                  (witness nvc-pair (held-pred 'x2) (pairN nil-nvc nil-nvc)
                           (conjoin (lohold (map-uppers nil-nvc one) 'x2)
                                    (uphold (map-uppers nil-nvc one) 'x2) triv triv)))))

(defn- feasible-step-witness []
  (function/lam [['k nat] ['fk (feasible (succ 'k))]] 'fk))

(defn- eliminate-witness []
  (function/lam [['n nat] ['init (feasible 'n)]] 'init))

(defn- partition-list-witness []
  (let [goal-pred (fn [x] (function/lam [['pr aff-pair]]
                                        (conj- (losat (p1a 'pr) x) (upsat (p2a 'pr) x))))]
    (function/lam [['rows list-bs] ['w R] ['red (reduced-conditions 'rows 'w)]]
                  (witness aff-pair (goal-pred 'w) (pairA nil-a nil-a)
                           (conjoin (losat nil-a 'w) (upsat nil-a 'w) triv triv)))))

;; CONTROL witness: the identity on the hypothesis h -- REJECTED, because
;; farkas-eliminate-base is substantive (add zero x is not definitional; the
;; add-zero-left transport is load-bearing). h : at-most (0 + c-l) (0 + c-r) is
;; NOT defeq the goal at-most c-l c-r.
(defn- eliminate-base-identity-witness []
  (function/lam [['c-l R] ['c-r R]
                 ['h (at-most (nn-add (eval-form nil-pair) 'c-l)
                              (nn-add (eval-form nil-pair) 'c-r))]]
                'h))

;; ---- harness: does the trivial inhabitant type-check against the theorem? ----
(defn- decl-type [env name]
  (:rainbow/type (environment/declaration env (environment/resolve-id env name))))

(defn- trivial-inhabits? [env surface type]
  (let [elab (elaborate/core-expression env surface)]
    (if (not= :elaborated (:status elab))
      {:status :elab-failed :detail (:message elab)}
      (kernel/check env (:term elab) type #{}))))

(defn- assert-still-vacuous [name witness]
  (let [env @checked-environment
        result (trivial-inhabits? env (witness) (decl-type env name))]
    (is (= :checked (:status result))
        (str name " is NO LONGER empty-satisfiable -- the trivial inhabitant "
             "was rejected (" (:status result) "). This theorem was STRENGTHENED. "
             "Good news: strike its entry in the design notes, "
             "note it in the design notes, and replace this negative test "
             "with a positive test for the new statement."))))

(deftest round-is-vacuous
  (testing "farkas-vector-round: the empty affine pair (nil,nil) inhabits its
            EXISTS-feasible-lists conclusion, ignoring all inputs"
    (assert-still-vacuous 'nnrat/farkas-vector-round round-witness)))

(deftest step-is-vacuous
  (testing "farkas-vector-step: the empty held pair (nil,nil) inhabits its
            EXISTS conclusion, ignoring all inputs"
    (assert-still-vacuous 'nnrat/farkas-vector-step step-witness)))

(deftest feasible-step-is-vacuous
  (testing "farkas-vector-feasible-step: the identity inhabits it (Feasible is
            uniform in k, so Feasible(succ k) is defeq Feasible k)"
    (assert-still-vacuous 'nnrat/farkas-vector-feasible-step feasible-step-witness)))

(deftest eliminate-is-vacuous
  (testing "farkas-vector-eliminate: the identity inhabits it (Feasible n defeq
            Feasible zero), so the eliminate-all fold is never exercised"
    (assert-still-vacuous 'nnrat/farkas-vector-eliminate eliminate-witness)))

(deftest partition-list-necessary-is-vacuous
  (testing "farkas-partition-list-necessary (PRE-EXISTING, shared): the
            empty affine pair inhabits its goal, ignoring rows AND the
            reduced-conditions hypothesis"
    (assert-still-vacuous 'nnrat/farkas-partition-list-necessary partition-list-witness)))

(deftest control-harness-is-not-a-rubber-stamp
  (testing "CONTROL for the five above. The harness must be able to say NO:
            farkas-eliminate-base is SUBSTANTIVE, so the identity candidate must
            be REJECTED. If this test fails, the harness is accepting anything
            (or eliminate-base changed) and every PASS above is meaningless --
            fix the harness before trusting the vacuity results."
    (let [env @checked-environment
          result (trivial-inhabits? env (eliminate-base-identity-witness)
                                    (decl-type env 'nnrat/farkas-eliminate-base))]
      (is (not= :checked (:status result))
          (str "the harness accepted the identity as a proof of the SUBSTANTIVE "
               "farkas-eliminate-base (status " (:status result) ") -- it is "
               "rubber-stamping. The five vacuity PASSES cannot be trusted until "
               "this is understood.")))))
