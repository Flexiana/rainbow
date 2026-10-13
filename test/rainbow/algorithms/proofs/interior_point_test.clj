(ns rainbow.algorithms.proofs.interior-point-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.interior-point :as barrier]
            [rainbow.algorithms.reference.interior-point :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (barrier/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest interior-point-barrier-is-native-axiom-free
  (let [env @checked-environment
        definitions (barrier/definition-ids env)
        theorems (barrier/theorem-ids env)]
    (is (= #{'barrier/objective} (set (keys definitions))))
    (is (= #{'barrier/objective-unfold 'barrier/unit-slack-example
             'barrier/wide-slack-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-interior-point-adds-inverse-barrier-exactly
  (is (= 3 (executable/barrier-objective 1 2 1)))
  (is (= 2 (executable/barrier-objective 1 2 2)))
  ;; As slack shrinks the barrier diverges: slack 1/2 gives 1 + 2/(1/2) = 5.
  (is (= 5 (executable/barrier-objective 1 2 1/2))))
