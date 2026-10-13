(ns rainbow.math.finite.signed-expectation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.signed-expectation :as expectation]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (expectation/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-signed-expectation-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (expectation/definition-ids env)
        theorems (expectation/theorem-ids env)]
    (is (= #{'probability/signed-total-mass
             'probability/signed-expectation}
           (set (keys definitions))))
    (is (= #{'probability/signed-expectation-monotone
             'probability/signed-expectation-add-constant
             'probability/signed-expectation-additive-upper-bound-normalized}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
