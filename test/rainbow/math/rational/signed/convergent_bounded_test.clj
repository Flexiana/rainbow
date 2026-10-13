(ns rainbow.math.rational.signed.convergent-bounded-test
  "Cold gate: a convergent sequence is bounded (brick 1 of limit-product)."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.convergent-bounded :as cb]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def ^:private env
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (cb/extend-environment (:environment checkpoint)))))

(defn- checked-and-axiom-free? [e alias]
  (let [id (environment/resolve-id e alias)
        d (environment/declaration e id)]
    (and id
         (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d)
                                            (set (:rainbow/universes d)))))
         (= #{} (kernel/axioms e id)))))

(deftest convergent-bounded-is-checked-and-axiom-free
  (testing "analysis/convergent-bounded: converges s L Ms -> |s n| <= 1 + |L| for n past Ms 1
            -- the first convergent=>bounded fact over signed sequences, prerequisite for
            limit-product"
    (is (checked-and-axiom-free? @env 'analysis/convergent-bounded))))
