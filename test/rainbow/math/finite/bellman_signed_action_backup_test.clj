(ns rainbow.math.finite.bellman-signed-action-backup-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-action-backup :as backup]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (backup/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-signed-action-backup-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (backup/definition-ids env)
        theorems (backup/theorem-ids env)]
    (is (= #{'bellman/signed-action-backup}
           (set (keys definitions))))
    (is (= #{'bellman/signed-action-backup-unfold
             'bellman/signed-action-backup-additive-upper-bound
             'bellman/signed-action-backup-additively-contractive}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
