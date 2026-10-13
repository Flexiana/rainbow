(ns rainbow.math.finite.nnrat-sup-radius-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.nnrat-sup-radius :as radius]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (radius/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-nnrat-sup-radius-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (radius/definition-ids env)
        theorems (radius/theorem-ids env)]
    (is (= #{'list/nnrat-map-max
             'metric/finite-nnrat-sup-radius}
           (set (keys definitions))))
    (is (= #{'list/nnrat-map-max-upper-bound
             'list/nnrat-map-max-bounded
             'list/nnrat-map-max-nonnegative
             'metric/finite-nnrat-sup-radius-upper-bound
             'metric/finite-nnrat-sup-radius-bounded
             'metric/finite-nnrat-sup-radius-nonnegative}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
