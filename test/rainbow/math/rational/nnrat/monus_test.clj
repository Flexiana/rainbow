(ns rainbow.math.rational.nnrat.monus-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.nnrat.monus :as nm]
            [rainbow.environment :as environment] [rainbow.kernel :as kernel]))
(def ^:private env (delay (nm/extend-environment (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")))))
(defn- caf? [e a] (let [id (environment/resolve-id e a) d (environment/declaration e id)]
  (and id (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d) #{}))) (= #{} (kernel/axioms e id)))))
(deftest nm
  (is (caf? @env 'nnrat/monus))
  (is (caf? @env 'nnrat/monus-add-cancel)))
