(ns rainbow.math.rational.binary.rational-order-test
  "Brick 5b: a Bin-native rational comparison proved to agree with the trusted
  checker's decision `audit/decide-nnrat-at-most`.

  Runs from a COLD JVM (lein test), reproducible from a clean environment. Verifies
  (1) the three declarations are checked + axiom-free; (2) the decision computes the
  right Bool on concrete Bin rationals (num/den built as Bin), including cases that
  need cross-multiplication; and (3) it is magnitude-independent: a comparison of
  rationals whose cross-products are ~2^40 (unreachable as unary Nat) checks
  essentially instantly -- the point of the whole binary-numeral lane."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.data.binary :as binary]
            [rainbow.math.rational.binary.rational-order :as bro]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]))

(def ^:private tl [:succ [:zero]])

(def ^:private env
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          binary/extend-environment
          bro/extend-environment))))

(defn- c [nm & a] (apply f/app (f/const* nm []) a))
(def ^:private bool (f/const* 'data/Bool []))
(def ^:private bz (f/const* 'data/bin-zero []))
(defn- be [x] (c 'data/bin-even x))
(defn- bo [x] (c 'data/bin-odd x))
;; Bin numeral for a small non-negative int, LSB-first via the constructors.
(defn- bin [n]
  (cond (zero? n) bz
        (even? n) (be (bin (quot n 2)))
        :else (bo (bin (quot n 2)))))
(defn- pow2 [k] (nth (iterate be (bo bz)) k))            ; 2^k
(def ^:private bval (fn [t] (if t (f/const* 'data/true []) (f/const* 'data/false []))))

(defn- checks? [e value type]
  (let [ve (elaborate/core-expression e value)
        te (elaborate/core-expression e type)]
    (and (= :elaborated (:status ve)) (= :elaborated (:status te))
         (= :checked (:status (kernel/check e (:term ve) (:term te) #{}))))))

(defn- checked-and-axiom-free? [e alias]
  (let [id (environment/resolve-id e alias)
        d (environment/declaration e id)]
    (and id
         (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d)
                                            (set (:rainbow/universes d)))))
         (= #{} (kernel/axioms e id)))))

(deftest bin-rational-order-is-checked-and-bridges-the-audit-decision
  (testing "bin/decide-rat-at-most (Bin cross-multiply-compare) is checked +
            axiom-free; it reflects the nat-level decision through to-nat
            (bin/decide-rat-at-most-reflects) and hence agrees with the trusted
            checker's audit/decide-nnrat-at-most whenever the Bin fields represent
            the rational's num/den (bin/decide-rat-matches-audit)."
    (let [e @env]
      (is (checked-and-axiom-free? e 'bin/decide-rat-at-most))
      (is (checked-and-axiom-free? e 'bin/decide-rat-at-most-reflects)
          "= nat/decide-at-most (num_l*den_r) (num_r*den_l), through to-nat")
      (is (checked-and-axiom-free? e 'bin/decide-rat-matches-audit)
          "= audit/decide-nnrat-at-most l r when to-nat of the Bin fields = num/den")
      ;; direct soundness: the Bin decision entails the checker's actual order
      (is (checked-and-axiom-free? e 'bin/decide-rat-at-most-true-sound)
          "decide=true -> nat/at-most (num_l*den_r) (num_r*den_l)")
      (is (checked-and-axiom-free? e 'bin/decide-rat-at-most-false-reverse)
          "decide=false -> the reverse cross order")
      (is (checked-and-axiom-free? e 'bin/decide-rat-sound)
          "decide=true -> nnrat/at-most l r (the trusted order), the 5c-ready form")
      (is (checked-and-axiom-free? e 'bin/decide-rat-false-reverse)
          "decide=false -> nnrat/at-most r l (the reverse trusted order)")
      ;; construction: nnrat/add's num/den built on Bin from the parts
      (is (checked-and-axiom-free? e 'bin/to-nat-rat-add-num)
          "to-nat(bin-add(np*dq)(nq*dp)) = numerator(nnrat/add p q)")
      (is (checked-and-axiom-free? e 'bin/to-nat-rat-add-den)
          "to-nat(bin-mul dp dq) = denominator(nnrat/add p q)"))))

(deftest bin-rational-decision-computes-correctly
  (testing "nl/dl <= nr/dr decided by cross-multiplication on Bin numerals equals the
            arithmetic truth, including cases that genuinely cross-multiply"
    (let [e @env
          decide (fn [nl dl nr dr] (c 'bin/decide-rat-at-most (bin nl) (bin dl) (bin nr) (bin dr)))
          truth (fn [nl dl nr dr] (<= (* nl dr) (* nr dl)))  ; nl/dl <= nr/dr
          eqk (fn [nl dl nr dr] (f/equality tl bool (decide nl dl nr dr) (bval (truth nl dl nr dr))))
          refl (fn [nl dl nr dr] (f/app (f/const* 'equality/reflexive [tl]) bool (bval (truth nl dl nr dr))))]
      (doseq [[nl dl nr dr] [[1 2 2 3]   ; 1/2 <= 2/3  true
                             [2 3 1 2]   ; 2/3 <= 1/2  false
                             [3 4 3 4]   ; equal       true
                             [5 6 4 5]   ; 25/30 vs 24/30 -> false
                             [1 3 1 2]   ; true
                             [7 2 3 1]   ; 7/2 <= 3/1 ? 7<=6 false
                             ;; edge cases: zero numerators and equal-by-different-reps
                             [0 5 1 1]   ; 0 <= 1        true
                             [0 3 0 7]   ; 0 <= 0        true
                             [1 2 2 4]   ; 1/2 = 2/4     true (equal, different reps)
                             [2 4 1 2]   ; 2/4 = 1/2     true (equal, reversed)
                             [3 1 3 1]]] ; 3/1 = 3/1     true
        (is (checks? e (refl nl dl nr dr) (eqk nl dl nr dr))
            (str nl "/" dl " <= " nr "/" dr " ? = " (truth nl dl nr dr)))))))

(deftest bin-rational-decision-is-magnitude-independent
  (testing "the cross-products reach ~2^40 (unreachable as unary Nat), yet the Bin
            decision checks essentially instantly -- the ceiling that walls the
            unary-Nat checker is gone for natively-Bin rationals"
    (let [e @env
          ;; 2^20 / 1  vs  (2^20 + 1) / 1  : cross-products are 2^20 and 2^20+1
          ;; and 2^40 / 1 vs 2^41 / 1 : cross-products 2^40, 2^41
          decide (fn [nl dl nr dr] (c 'bin/decide-rat-at-most nl dl nr dr))
          refl (fn [t] (f/app (f/const* 'equality/reflexive [tl]) bool (bval t)))
          eqk (fn [nl dl nr dr t] (f/equality tl bool (decide nl dl nr dr) (bval t)))
          one (bo bz)]
      ;; 2^40/1 <= 2^41/1  ->  2^40 <= 2^41  true
      (is (checks? e (refl true) (eqk (pow2 40) one (pow2 41) one true))
          "2^40/1 <= 2^41/1")
      ;; 2^41/1 <= 2^40/1  ->  false
      (is (checks? e (refl false) (eqk (pow2 41) one (pow2 40) one false))
          "2^41/1 <= 2^40/1 is false"))))
