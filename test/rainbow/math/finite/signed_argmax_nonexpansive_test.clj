(ns rainbow.math.finite.signed-argmax-nonexpansive-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.signed-argmax-nonexpansive :as nonexpansive]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (nonexpansive/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-signed-argmax-nonexpansiveness-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (nonexpansive/definition-ids env)
        theorems (nonexpansive/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'decision/finite-signed-argmax-additive-upper-bound
             'decision/finite-signed-argmax-additively-nonexpansive}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
