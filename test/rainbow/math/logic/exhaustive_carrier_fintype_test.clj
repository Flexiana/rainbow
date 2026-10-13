(ns rainbow.math.logic.exhaustive-carrier-fintype-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.exhaustive-carrier-fintype :as bridge]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (bridge/extend-environment (:environment checkpoint)))))

(defn- checked? [env alias]
  (let [id (environment/resolve-id env alias)
        declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest exhaustive-computational-carrier-constructs-extensional-fintype
  (let [env @checked-environment]
    (is (= #{'finite/fintype-of-certified-exhaustive-carrier}
           (set (keys (bridge/definition-ids env)))))
    (is (= #{'finite/fintype-elements-of-certified-exhaustive-carrier
             'finite/type-finite-of-certified-exhaustive-carrier}
           (set (keys (bridge/theorem-ids env)))))
    (doseq [alias (concat (keys (bridge/definition-ids env))
                          (keys (bridge/theorem-ids env)))]
      (is (checked? env alias) (str alias))
      (is (= #{} (kernel/axioms env (environment/resolve-id env alias)))
          (str alias)))))
