(ns rainbow.math.rational.signed.absolute-sign-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.absolute-sign :as asign]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))
(def ^:private env
  (delay
    (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status cp)) (throw (ex-info "D63 rejected" {})))
      (asign/extend-environment (:environment cp)))))
(defn- caf? [e alias]
  (let [id (environment/resolve-id e alias) d (environment/declaration e id)]
    (and id (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d)))))
         (= #{} (kernel/axioms e id)))))
(deftest absolute-sign-checked
  (testing "|w|~w for 0<=w and |w|~-w for w<=0, axiom-free"
    (is (caf? @env 'signed/absolute-of-nonnegative))
    (is (caf? @env 'signed/absolute-of-nonpositive))))
