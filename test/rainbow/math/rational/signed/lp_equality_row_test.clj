(ns rainbow.math.rational.signed.lp-equality-row-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.lp-equality-row :as row]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (-> (:environment r) row/extend-environment decide/extend-environment))))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(defn- core! [expression]
  (let [r (elaborate/core-expression @env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- check [label value target]
  (let [r (kernel/check @env (core! value) (core! target) #{})
        result {:status (:status r) :category (get-in r [:error :error/category])}]
    (println "LP-EQUALITY-ROW" label (pr-str result))
    result))

(deftest generic-row-equivalence-is-kernel-checked-and-axiom-free
  (doseq [[name id] (row/theorem-ids @env)]
    (let [d (environment/declaration @env id)
          r (kernel/check @env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d)))]
      (println "LP-EQUALITY-THEOREM" name id (:status r) (kernel/axioms @env id))
      (is (some? id))
      (is (= :checked (:status r)))
      (is (= #{} (kernel/axioms @env id))))))

(deftest empty-repeated-signed-and-one-sided-counterexamples
  (doseq [[coefficients values indices bound valid?]
          [[[1] [1] [] 0 true]
           [[1 2] [2 1] [0 1 1] 6 true]
           [[2 -3] [1 2] [0 1 1] -10 true]
           [[2 -3] [1 2] [0 1 1] -9 false]
           [[2 -3] [1 2] [0 1 1] -11 false]]]
    (let [mapping (fn [v] (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal v)))
          a (mapping coefficients) x (mapping values)
          index-list (reduce (fn [tail i]
                               (f/app (f/const* 'data/cons [[:succ [:zero]]]) lp/nat (#'lp/numeral i) tail))
                             (f/app (f/const* 'data/nil [[:succ [:zero]]]) lp/nat) (reverse indices))
          b (#'lp/signed-literal bound)
          negative-a (f/lam [['i lp/nat]] (app 'signed/negate (f/app a 'i)))
          objective (fn [c] (poly 'signed/map-sum lp/nat
                                 (f/lam [['i lp/nat]]
                                        (app 'signed/multiply (f/app c 'i) (f/app x 'i))) index-list))
          original (objective a) negative (objective negative-a)
          P (app 'signed/at-most original b)
          Q (app 'signed/at-most negative (app 'signed/negate b))
          pair (app 'proposition/conjunction P Q)
          pair-proof (app 'proposition/conjoin P Q
                          (#'lp/decided-at-most original b)
                          (#'lp/decided-at-most negative (app 'signed/negate b)))
          expand (poly 'signed/lp-equality-row-expand lp/nat a x index-list b
                       (#'lp/computed-equivalence original b))
          contract (poly 'signed/lp-equality-row-contract lp/nat a x index-list b pair-proof)
          eq-target (app 'signed/equivalent original b)]
      (doseq [[direction proof target] [[:expand expand pair] [:contract contract eq-target]]]
        (let [r (check [direction bound indices] proof target)]
          (is (= (if valid? :checked :rejected) (:status r)))
          (when-not valid? (is (= :kernel/type-mismatch (:category r)))))))))
