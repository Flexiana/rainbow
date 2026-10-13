(ns rainbow.algorithms.proofs.ahof.floyd-cycle-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.floyd-cycle :as floyd]
            [rainbow.algorithms.reference.floyd-cycle :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          floyd/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest floyd-cycle-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (floyd/definition-ids checked-environment)
        theorems (floyd/theorem-ids checked-environment)]
    (is (= #{'floyd-cycle/meet?} (set (keys definitions))))
    (is (= #{'floyd-cycle/same-position-detects-cycle
             'floyd-cycle/meeting-positions-coincide
             'floyd-cycle/different-position-no-meeting}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-floyd-cycle
  (is (true? (executable/meet? 4 4)))
  (is (false? (executable/meet? 2 5)))
  ;; f(x) = (x+1) mod 6 cycles through 0..5; detect a cycle
  (is (true? (executable/has-cycle? #(mod (inc %) 6) 0 :end)))
  ;; a terminating sequence (decrement to a sentinel) has no cycle
  (is (false? (executable/has-cycle? #(if (zero? %) :end (dec %)) 5 :end))))
