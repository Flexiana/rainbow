(ns rainbow.math.rational.nnrat.radius-cancel-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.nnrat.radius-cancel :as rc]
            [rainbow.environment :as environment] [rainbow.kernel :as kernel]))
(def ^:private env (delay (rc/extend-environment (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")))))
(defn- caf? [e a] (let [id (environment/resolve-id e a) d (environment/declaration e id)]
  (and id (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d) #{}))) (= #{} (kernel/axioms e id)))))
(deftest rc (is (caf? @env 'analysis/nnrat-radius-cancel)))
