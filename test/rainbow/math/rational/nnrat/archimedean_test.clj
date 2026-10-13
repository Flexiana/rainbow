(ns rainbow.math.rational.nnrat.archimedean-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.archimedean :as arch]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (arch/extend-environment (:environment checkpoint)))))

(defn- checked-status [env id]
  (let [declaration (environment/declaration env id)]
    (:status
     (kernel/check env (:rainbow/value declaration)
                   (:rainbow/type declaration)
                   (set (:rainbow/universes declaration))))))

(deftest nnrat-archimedean-is-kernel-checked-and-axiom-free
  (let [env @checked-environment
        declarations
        (merge (arch/definition-ids env) (arch/theorem-ids env))]
    (is (= #{'nnrat/at-most-of-all-plus-reciprocal}
           (set (keys declarations))))
    (doseq [[name id] declarations]
      (is (= :checked (checked-status env id)) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
