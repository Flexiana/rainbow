(ns rainbow.math.rational.signed.close-radius-monotone-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.close-radius-monotone :as crm]
            [rainbow.environment :as environment] [rainbow.kernel :as kernel]))
(def ^:private env (delay (crm/extend-environment (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")))))
(defn- caf? [e a] (let [id (environment/resolve-id e a) d (environment/declaration e id)]
  (and id (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d) #{}))) (= #{} (kernel/axioms e id)))))
(deftest crm (is (caf? @env 'analysis/close-radius-monotone)))
