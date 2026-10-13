(ns rainbow.algorithms.proofs.ahof.edmonds-karp-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.edmonds-karp :as ek]
            [rainbow.algorithms.reference.edmonds-karp :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ek/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest edmonds-karp-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ek/definition-ids checked-environment)
        theorems (ek/theorem-ids checked-environment)]
    (is (= #{'edmonds-karp/has-residual?} (set (keys definitions))))
    (is (= #{'edmonds-karp/positive-residual-usable
             'edmonds-karp/usable-residual-at-least-one
             'edmonds-karp/saturated-edge-unusable}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-edmonds-karp
  (is (true? (executable/has-residual? 3)))
  (is (false? (executable/has-residual? 0)))
  ;; classic CLRS network, max flow 0->5 is 23
  (let [edges {[0 1] 16 [0 2] 13 [1 2] 10 [2 1] 4 [1 3] 12
               [3 2] 9 [2 4] 14 [4 3] 7 [3 5] 20 [4 5] 4}]
    (is (= 23 (executable/max-flow edges 6 0 5)))))
