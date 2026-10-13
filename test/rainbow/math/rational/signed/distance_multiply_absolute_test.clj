(ns rainbow.math.rational.signed.distance-multiply-absolute-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.distance-multiply-absolute :as dma]
            [rainbow.environment :as environment] [rainbow.kernel :as kernel]))
(def ^:private env (delay (dma/extend-environment (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")))))
(defn- caf? [e a] (let [id (environment/resolve-id e a) d (environment/declaration e id)]
  (and id (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d) #{}))) (= #{} (kernel/axioms e id)))))
(deftest dma (is (caf? @env 'analysis/distance-multiply-left-absolute)))
