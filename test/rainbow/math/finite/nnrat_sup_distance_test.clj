(ns rainbow.math.finite.nnrat-sup-distance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.nnrat-sup-distance :as metric]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (metric/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-nnrat-sup-distance-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (metric/definition-ids env)
        theorems (metric/theorem-ids env)]
    (is (= #{'metric/finite-nnrat-sup-distance}
           (set (keys definitions))))
    (is (= #{'list/signed-map-max-upper-bound
             'metric/finite-nnrat-sup-distance-upper-bound
             'metric/finite-nnrat-sup-distance-bounded
             'metric/finite-nnrat-sup-distance-nonnegative
             'metric/finite-nnrat-sup-distance-symmetric
             'metric/finite-nnrat-sup-distance-triangle}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
