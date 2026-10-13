(ns rainbow.algorithms.proofs.ahof.gradient-clipping-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gradient-clipping :as gc]
            [rainbow.algorithms.reference.gradient-clipping :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          gc/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest gradient-clipping-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (gc/definition-ids checked-environment)
        theorems (gc/theorem-ids checked-environment)]
    (is (= #{'gradient-clipping/clips?} (set (keys definitions))))
    (is (= #{'gradient-clipping/large-gradient-clipped
             'gradient-clipping/clipped-exceeds-threshold
             'gradient-clipping/small-gradient-unclipped}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-gradient-clipping
  (is (true? (executable/clips? 7 5)))
  (is (false? (executable/clips? 3 5)))
  ;; gradient [3 4] has norm 5; clip to 1 -> norm 1
  (let [g (executable/clip [3 4] 1)]
    (is (< (abs (- 1.0 (Math/sqrt (reduce + (map #(* % %) g))))) 1e-9)))
  ;; small gradient unchanged
  (is (= [1 0] (executable/clip [1 0] 5))))
