(ns rainbow.math.rational.signed.distance-negate-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.distance-negate :as dn]
            [rainbow.environment :as environment] [rainbow.kernel :as kernel]))
(def ^:private env (delay (dn/extend-environment (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")))))
(defn- caf? [e a] (let [id (environment/resolve-id e a) d (environment/declaration e id)]
  (and id (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d) #{}))) (= #{} (kernel/axioms e id)))))
(deftest dnb (is (caf? @env 'signed/distance-negate-both)))
