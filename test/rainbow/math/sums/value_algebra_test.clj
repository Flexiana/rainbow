(ns rainbow.math.sums.value-algebra-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as m]
            [rainbow.or.lp-certificate :as literals]))

(def checked-environment
  (delay
    (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status cp)) (throw (ex-info "Checkpoint rejected" {})))
      (m/extend-environment (:environment cp)))))

(defn- core! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- check [label proof target expected]
  (let [env @checked-environment
        r (kernel/check env (core! env proof) (core! env target) #{})]
    (println :control label (:status r))
    (is (= expected (:status r)) (str label))
    (when (= expected :rejected)
      (is (= :kernel/type-mismatch (get-in r [:error :error/category])) (str label)))))
(defn- lit [n] (#'literals/signed-literal n))
(defn- nn [n] (nth (iterate m/succ m/nz) n))
(defn- const-fn [x] (f/lam [['i m/nat]] x))
(defn- comparison [a b] (#'literals/decided-at-most a b))
(defn- bounded-proof [n proof]
  (f/lam [['idx m/nat] ['bound (m/below 'idx n)]] proof))

(deftest finite-sum-algebra-is-kernel-checked-and-axiom-free
  (let [env @checked-environment ids (m/theorem-ids env)]
    (is (= 11 (count ids)))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)
            r (kernel/check env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d)))
            axioms (kernel/axioms env id)]
        (println name (:status r) :axioms axioms)
        (is (= :checked (:status r)) (str name))
        (is (= #{} axioms) (str name))))))

(deftest arithmetic-laws-have-inhabitants-and-reject-false-instances
  ;; Nonempty, unequal dimensions make omitted summands/scalars/bounds visible.
  ;; Negative c is deliberately admitted by scaling; it has no sign premise.
  (let [F (const-fn (lit 1)) G (const-fn (lit 2)) n (nn 2) k (nn 3)
        plus (const-fn (m/add (lit 1) (lit 2)))
        matrix (f/lam [['i m/nat] ['j m/nat]] (lit 1))
        nested (m/sum (const-fn (m/sum F k)) n)]
    (doseq [[label proof lhs rhs wrong]
            [[:bridge (m/call 'signed/expr-sum-value-as-map-sum F n)
              (m/sum F n) (m/map-sum F n) (m/map-sum F k)]
             [:zero (m/call 'signed/expr-sum-value-zero n)
              (m/sum (const-fn m/zero) n) m/zero (lit 1)]
             [:add (m/call 'signed/expr-sum-value-add F G n)
              (m/sum plus n) (m/add (m/sum F n) (m/sum G n)) (m/sum F n)]
             [:scale-right (m/call 'signed/expr-sum-value-scale-right F (lit -2) k)
              (m/mul (m/sum F k) (lit -2)) (m/sum (const-fn (m/mul (lit 1) (lit -2))) k) (m/sum F k)]
             [:scale-left (m/call 'signed/expr-sum-value-scale-left F (lit -2) k)
              (m/mul (lit -2) (m/sum F k)) (m/sum (const-fn (m/mul (lit -2) (lit 1))) k) (m/sum F k)]
             [:swap (m/call 'signed/expr-sum-value-swap matrix k n)
              nested (m/sum (const-fn (m/sum F n)) k) (m/sum (const-fn (m/sum F n)) n)]]]
      (check [label :inhabited] proof (m/eqv lhs rhs) :checked)
      (check [label :false] proof (m/eqv lhs wrong) :rejected))))

(deftest bounded-laws-have-satisfiable-load-bearing-premises
  (let [n (nn 1) F (const-fn (lit 1)) G (const-fn (lit 2))
        ordered (bounded-proof n (comparison (lit 1) (lit 2)))
        reversed (bounded-proof n (comparison (lit 2) (lit 1)))
        same (bounded-proof n (m/refl (lit 1)))
        forged-same (bounded-proof n (#'literals/computed-equivalence (lit 1) (lit 2)))]
    (check :bounds-inhabited (m/call 'signed/expr-sum-bounds-as-list F G n ordered)
           (m/listed-le F G n) :checked)
    (check :bounds-false (m/call 'signed/expr-sum-bounds-as-list G F n reversed)
           (m/listed-le G F n) :rejected)
    (check :monotone-inhabited (m/call 'signed/expr-sum-value-monotone-below F G n ordered)
           (m/le (m/sum F n) (m/sum G n)) :checked)
    (check :monotone-false (m/call 'signed/expr-sum-value-monotone-below G F n reversed)
           (m/le (m/sum G n) (m/sum F n)) :rejected)
    (check :congruence-inhabited (m/call 'signed/expr-sum-value-respects-equivalence-below F F n same)
           (m/eqv (m/sum F n) (m/sum F n)) :checked)
    (check :congruence-false (m/call 'signed/expr-sum-value-respects-equivalence-below F G n forged-same)
           (m/eqv (m/sum F n) (m/sum G n)) :rejected)
    (doseq [left? [true false] w [2 -1]]
      (let [W (const-fn (lit w))
            product (fn [g] (f/lam [['i m/nat]]
                                  (if left? (m/mul (m/at W 'i) (m/at g 'i))
                                      (m/mul (m/at g 'i) (m/at W 'i)))))
            name (if left? 'signed/expr-sum-value-weighted-monotone-left
                     'signed/expr-sum-value-weighted-monotone-right)
            proof (m/call name W F G n (bounded-proof n (comparison m/zero (lit w))) ordered)]
        (check [name w] proof (m/le (m/sum (product F) n) (m/sum (product G) n))
               (if (pos? w) :checked :rejected))))))
