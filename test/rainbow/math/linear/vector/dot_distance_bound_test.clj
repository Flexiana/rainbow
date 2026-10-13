(ns rainbow.math.linear.vector.dot-distance-bound-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.vector.dot-distance-bound :as laws]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (laws/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest vector-dot-distance-bound-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)
        declarations (merge definitions theorems)]
    (is (= #{'vector/dot-distance-sum}
           (set (keys definitions))))
    (is (= #{'vector/dot-distance-below-sum
             'vector/dot-distance-bounded}
           (set (keys theorems))))
    (doseq [[name id] declarations]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
