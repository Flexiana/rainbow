(ns rainbow.math.rational.signed.vector-sup-distance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.vector-sup-distance :as laws]))

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

(deftest signed-vector-sup-distance-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)
        declarations (merge definitions theorems)]
    (is (= #{'list/signed-map-max 'vector/sup-distance 'vector/within}
           (set (keys definitions))))
    (is (= #{'list/signed-map-max-empty
             'signed/equivalent-of-equality
             'list/signed-map-max-cons
             'list/signed-map-max-nonnegative
             'list/signed-map-max-bounded
             'list/signed-map-max-congruent
             'vector/sup-distance-empty-left
             'vector/sup-distance-empty-right
             'vector/sup-distance-cons
             'vector/sup-distance-nonnegative
             'vector/sup-distance-cons-bounded
             'vector/sup-distance-bounded
             'vector/sup-distance-cons-symmetric
             'vector/sup-distance-empty-symmetric
             'vector/sup-distance-cons-empty-symmetric
             'vector/sup-distance-cons-symmetric-all
             'vector/sup-distance-symmetric
             'vector/sup-distance-self-zero}
           (set (keys theorems))))
    (doseq [[name id] declarations]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
