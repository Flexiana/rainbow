(ns rainbow.math.finite.bellman-signed-greedy-policy-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-greedy-policy
             :as greedy]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (greedy/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest signed-greedy-policy-certificate-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (greedy/definition-ids env)
        theorems (greedy/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'value/nnrat-transition-signed-greedy-policy-is-admissible
             'value/nnrat-transition-signed-greedy-policy-attains-fixed-value
             'value/nnrat-transition-signed-greedy-fixed-point-policy-certificate}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
