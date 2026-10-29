(ns rainbow.or.lp-scaling-bridge-test
  "Banks the reproducible facts about the verified-scaling bridge -- the EXPERIMENTAL,
  unwired producer `transported-bound-spec` that would kernel-certify integerize's
  original-unit bound by transporting the scaled certificate through axiom-free scaling theorems.

  Runs from a COLD JVM (no warm-nREPL dependency), so the finding is reproducible
  by anyone via `lein test rainbow.or.lp-scaling-bridge-test`, not only in a live
  session. The multi-dimension reduction-cost wall is a performance observation
  (kept out of the suite, not a flaky timing test), while the STABLE facts banked here
  are:

    1. the 1-dimension transport is :checked and axiom-free -- the mechanism is
       sound and the reference implementation is correct;
    2. it is TAMPER-EVIDENT -- the same proof checked against an altered host
       endpoint (a different margin) is rejected, so the certificate genuinely
       binds to the actual reported numbers, not to substituted formal lambdas.

  The bridge is not wired into `bound` and is not a soundness requirement -- the
  LP checker's equality-scaling soundness is fixed and guarded elsewhere."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.math.rational.signed.lp-scaling-bound :as slb]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private env
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          lp-on/extend-environment
          decide-order/extend-environment
          slb/extend-environment))))

(def ^:private standard-form (deref #'lp/standard-form))
(def ^:private transported-bound-spec (deref #'lp/transported-bound-spec))

(defn- check-status [e value type]
  (let [ve (elaborate/core-expression e value)
        te (elaborate/core-expression e type)]
    (if (and (= :elaborated (:status ve)) (= :elaborated (:status te))
             (:term ve) (:term te))
      (:status (kernel/check e (:term ve) (:term te) #{}))
      :elaboration-failed)))

(defn- spec-for [instance]
  (let [[scaled D] (lp/integerize instance)]
    (transported-bound-spec 'optimization/bridge-test
                            (standard-form instance) (standard-form scaled) D)))

(def ^:private one-col
  {:matrix [[1]] :capacities [1] :margins [1] :plan [1/2] :prices [1]})
(def ^:private one-col-altered
  {:matrix [[1]] :capacities [1] :margins [2] :plan [1/2] :prices [1]})

(deftest one-dimension-transport-is-checked
  (testing "the experimental scaling-bridge producer certifies the original
            bound-spec at one dimension (reference implementation is sound)"
    (let [e @env
          spec (spec-for one-col)]
      (is (= :checked (check-status e (:value spec) (:type spec)))))))

(deftest transport-is-tamper-evident
  (testing "the transport binds to the actual host endpoints: a valid proof
            checked against an ALTERED-margin type is rejected"
    (let [e @env
          valid (spec-for one-col)
          altered (spec-for one-col-altered)]
      ;; sanity: the valid proof checks against its own type
      (is (= :checked (check-status e (:value valid) (:type valid))))
      ;; tamper: it must NOT check against the altered-endpoint type
      (is (not= :checked (check-status e (:value valid) (:type altered)))
          "a proof for one instance checked against an altered host endpoint's type
           must be rejected -- otherwise the certificate is not bound to the actual
           reported numbers"))))
