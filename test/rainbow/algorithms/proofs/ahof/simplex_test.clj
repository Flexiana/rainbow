(ns rainbow.algorithms.proofs.ahof.simplex-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.simplex :as simplex]
            [rainbow.algorithms.reference.simplex :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          simplex/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest simplex-pivot-ratio-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (simplex/definition-ids checked-environment)
        theorems (simplex/theorem-ids checked-environment)]
    (is (= #{'simplex/pivot-ratio} (set (keys definitions))))
    (is (= #{'simplex/pivot-example
             'simplex/pivot-below-r1
             'simplex/pivot-below-r2}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-simplex-min-ratio-test
  (is (= 2 (executable/pivot-ratio 7 2)))
  ;; rhs [6 8 5], column [2 1 5]: ratios 3, 8, 1 -> row 2 leaves (ratio 1).
  (is (= 2 (executable/leaving-row [6 8 5] [2 1 5])))
  ;; A non-positive column entry is ignored; unbounded column -> nil.
  (is (nil? (executable/leaving-row [6 8] [0 -1]))))
