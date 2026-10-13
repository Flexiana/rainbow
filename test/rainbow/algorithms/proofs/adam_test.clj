(ns rainbow.algorithms.proofs.adam-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.adam :as adam]
            [rainbow.algorithms.reference.adam :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (adam/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest adam-first-moment-and-direction-are-native-axiom-free
  (let [env @checked-environment
        definitions (adam/definition-ids env)
        theorems (adam/theorem-ids env)]
    (is (= #{'adam/first-moment 'adam/direction} (set (keys definitions))))
    (is (= #{'adam/first-moment-unfold 'adam/first-moment-example
             'adam/direction-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-adam-preconditions-exactly
  ;; First moment from zero: 1/2*0 + 1/2*2 = 1.
  (is (= 1 (executable/first-moment 1/2 1/2 0 2)))
  ;; Preconditioned direction: first moment 1 over sqrt(4)=2 gives 1/2.
  (is (= 1/2 (executable/direction 1 4)))
  (is (= 2/3 (executable/direction 2 9))))
