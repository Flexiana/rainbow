(ns rainbow.math.rational.nnrat.positive-succ-form-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.nnrat.positive-succ-form :as psf]
            [rainbow.environment :as environment] [rainbow.kernel :as kernel]))
(def ^:private env (delay (psf/extend-environment (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")))))
(defn- caf? [e a] (let [id (environment/resolve-id e a) d (environment/declaration e id)]
  (and id (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d) #{}))) (= #{} (kernel/axioms e id)))))
(deftest psf
  (is (caf? @env 'nat/successor-of-predecessor))
  (is (caf? @env 'nnrat/make-succ-of-positive-numerator)))
