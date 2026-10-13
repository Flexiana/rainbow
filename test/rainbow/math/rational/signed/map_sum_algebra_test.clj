(ns rainbow.math.rational.signed.map-sum-algebra-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.map-sum-algebra :as algebra]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (algebra/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-map-sum-algebra-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (algebra/definition-ids env) (algebra/theorem-ids env))]
    (is (= #{'signed/add-respects-equivalence
             'signed/add-four-reorder
             'signed/equivalent-transitive
             'signed/map-sum-respects-equivalence
             'signed/map-sum-zero
             'signed/map-sum-add
             'signed/weighted-sum-monotone}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
