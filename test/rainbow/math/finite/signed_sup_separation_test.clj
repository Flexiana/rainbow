(ns rainbow.math.finite.signed-sup-separation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.signed-sup-separation :as separation]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (separation/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-signed-sup-separation-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (separation/definition-ids env)
        theorems (separation/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'metric/finite-signed-sup-distance-zero-of-pointwise-equivalent
             'metric/pointwise-equivalent-of-finite-signed-sup-distance-zero
             'metric/finite-signed-sup-distance-zero-iff-pointwise-equivalent}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
