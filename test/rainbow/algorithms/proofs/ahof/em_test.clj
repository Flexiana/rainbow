(ns rainbow.algorithms.proofs.ahof.em-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.em :as em]
            [rainbow.algorithms.reference.em :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          em/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest em-monotone-ascent-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (em/definition-ids checked-environment)
        theorems (em/theorem-ids checked-environment)]
    (is (= #{'em/improves?} (set (keys definitions))))
    (is (= #{'em/iteration-ascends 'em/never-decreases-likelihood
             'em/converged-at-fixed-point}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-em-ascends-to-fixed-point
  (is (true? (executable/improves? 8 5)))
  (is (true? (executable/improves? 8 8)))
  ;; Likelihood 0 -> min(prev+3, 10): climbs 0,3,6,9,10,10 and stops at 10.
  (let [step (fn [l] (let [nl (min (+ l 3) 10)] [nl nl]))
        [_ l] (executable/em step identity 0 20)]
    (is (= 10 l))))
