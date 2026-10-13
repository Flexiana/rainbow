(ns rainbow.math.analysis.geometric-decay-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.analysis.geometric-decay :as decay]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (decay/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest geometric-decay-is-native-axiom-free
  (let [env @checked-environment
        definitions (decay/definition-ids env)
        theorems (decay/theorem-ids env)]
    (is (= #{'decay/contract} (set (keys definitions))))
    (is (= #{'decay/contract-unfold 'decay/step1-eight-to-four
             'decay/step2-four-to-two 'decay/step3-two-to-one
             'decay/three-steps-eight-to-one} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-geometric-decay-halves-toward-zero
  (let [contract (fn [gamma d] (* gamma d))]
    (is (= 4 (contract 1/2 8)))
    (is (= 2 (contract 1/2 4)))
    (is (= 1 (contract 1/2 2)))
    ;; gamma^3 * 8 = 1.
    (is (= 1 (contract 1/2 (contract 1/2 (contract 1/2 8)))))
    ;; The geometric modulus: gamma^n * 8 < 1/2 once n >= 5 (8/2^5 = 1/4).
    (is (< (* (Math/pow 1/2 5) 8) 1/2))))
