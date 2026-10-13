(ns rainbow.math.rational.signed.limit-scale-law-test
  "Cold gate for the scalar-multiple limit law (limit linearity's scaling piece)."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.limit-scale-law :as lsl]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def ^:private env
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (lsl/extend-environment (:environment checkpoint)))))

(defn- checked-and-axiom-free? [e alias]
  (let [id (environment/resolve-id e alias)
        d (environment/declaration e id)]
    (and id
         (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d)
                                            (set (:rainbow/universes d)))))
         (= #{} (kernel/axioms e id)))))

(deftest limit-scale-is-checked-and-axiom-free
  (testing "analysis/limit-scale (n |-> c*s n converges to c*L for positive c) and its
            supporting radius-cancellation lemma are checked + axiom-free, completing
            the linearity of the limit operator alongside limit-sum/difference/negate/const"
    (let [e @env]
      (is (checked-and-axiom-free? e 'analysis/scale-reciprocal-radius-cancel)
          "(from-nnrat c)*((from-nnrat 1/c)*d) ~ d for c=(succ p)/q")
      (is (checked-and-axiom-free? e 'analysis/limit-scale)
          "converges s L M -> converges (n|->c*s n) (c*L) (eps|->M(1/c*eps))"))))
