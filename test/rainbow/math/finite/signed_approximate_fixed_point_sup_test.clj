(ns rainbow.math.finite.signed-approximate-fixed-point-sup-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.signed-approximate-fixed-point-sup
             :as laws]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (laws/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest pointwise-approximate-fixed-points-yield-finite-sup-certificates
  (let [env @checked-environment
        theorems (laws/theorem-ids env)]
    (is (empty? (laws/definition-ids env)))
    (is (= #{'metric/finite-signed-sup-distance-bounded-by-pointwise-additive-closeness
             'value/signed-pointwise-approximate-fixed-point-sup-certificate
             'value/signed-pointwise-approximate-fixed-point-existence-gives-sup-existence}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
