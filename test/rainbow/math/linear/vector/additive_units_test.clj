(ns rainbow.math.linear.vector.additive-units-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.vector.additive-units :as units]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (units/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest vector-additive-units-are-native-and-axiom-free
  (let [env @checked-environment
        definitions (units/definition-ids env)
        theorems (units/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= #{'vector/zero-like} (set (keys definitions))))
    (is (= #{'vector/add-zero-like-right
             'vector/add-zero-like-left
             'vector/subtract-self-equivalent-zero-like
             'vector/add-negate-right-equivalent-zero-like
             'vector/add-negate-left-equivalent-zero-like}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
