(ns rainbow.math.linear.vector.shape-cancellation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.vector.shape-cancellation :as cancellation]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (cancellation/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest vector-shape-and-cancellation-laws-are-native-and-axiom-free
  (let [env @checked-environment
        definitions (cancellation/definition-ids env)
        theorems (cancellation/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= #{'vector/same-shape} (set (keys definitions))))
    (is (= #{'vector/same-shape-reflexive
             'vector/same-shape-symmetric
             'vector/same-shape-transitive
             'vector/subtract-add-right-cancel
             'vector/add-subtract-right-cancel}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
