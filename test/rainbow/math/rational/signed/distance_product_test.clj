(ns rainbow.math.rational.signed.distance-product-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.distance-product :as dp]
            [rainbow.environment :as environment] [rainbow.kernel :as kernel]))
(def ^:private env (delay (dp/extend-environment (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")))))
(defn- caf? [e a] (let [id (environment/resolve-id e a) d (environment/declaration e id)]
  (and id (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d) #{}))) (= #{} (kernel/axioms e id)))))
(deftest dp
  (is (caf? @env 'signed/distance-multiply-right-absolute))
  (is (caf? @env 'analysis/distance-product)))
