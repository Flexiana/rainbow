(ns rainbow.algorithms.proofs.ahof.gaussian-inference-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gaussian-inference :as gaussian]
            [rainbow.algorithms.reference.gaussian-inference :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          gaussian/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest gaussian-inference-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (gaussian/definition-ids checked-environment)
        theorems (gaussian/theorem-ids checked-environment)]
    (is (= #{'gaussian/posterior-precision} (set (keys definitions))))
    (is (= #{'gaussian/posterior-precision-unfold
             'gaussian/posterior-precision-example
             'gaussian/precision-increases}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-gaussian-conjugate-posterior
  (is (= 5 (executable/posterior-precision 2 3)))
  ;; Prior N(mean 0, precision 2), observe value 5 with precision 3:
  ;; posterior precision 5, mean (2*0 + 3*5)/5 = 3.
  (let [post (executable/posterior 0 2 5 3)]
    (is (= 5 (:precision post)))
    (is (= 3 (:mean post)))))
