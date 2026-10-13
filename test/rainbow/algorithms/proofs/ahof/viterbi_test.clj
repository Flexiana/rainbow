(ns rainbow.algorithms.proofs.ahof.viterbi-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.viterbi :as viterbi]
            [rainbow.algorithms.reference.viterbi :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          viterbi/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest viterbi-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (viterbi/definition-ids checked-environment)
        theorems (viterbi/theorem-ids checked-environment)]
    (is (= #{'viterbi/path-prob 'viterbi/cell} (set (keys definitions))))
    (is (= #{'viterbi/path-prob-example 'viterbi/keeps-most-probable
             'viterbi/survivor-dominates}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-viterbi
  (is (= 1/4 (executable/path-prob 1/2 1/2 1)))
  (is (= 1/2 (executable/cell 1/4 1/2)))
  ;; 2-state HMM, obs [0 0], symmetric; best path prob = (1/2)*(1)*(1/2)*(1)=1/4
  (is (= 1/4 (executable/decode 2 [0 0]
                                (fn [_] 1/2) (fn [_ _] 1/2) (fn [_ _] 1)))))
