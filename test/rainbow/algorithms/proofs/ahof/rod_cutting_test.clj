(ns rainbow.algorithms.proofs.ahof.rod-cutting-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.rod-cutting :as rod]
            [rainbow.algorithms.reference.rod-cutting :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          rod/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest rod-cutting-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (rod/definition-ids checked-environment)
        theorems (rod/theorem-ids checked-environment)]
    (is (= #{'rod-cutting/cell} (set (keys definitions))))
    (is (= #{'rod-cutting/takes-better-cut 'rod-cutting/keeps-best-cut
             'rod-cutting/dominates-cut 'rod-cutting/dominates-previous}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-rod-cutting
  (is (= 8 (executable/cell 5 8)))
  (is (= 7 (executable/cell 7 3)))
  ;; classic prices [1 5 8 9 10 17 17 20], rod length 4 -> 10 (two length-2 cuts)
  (is (= 10 (executable/max-revenue 4 [1 5 8 9 10 17 17 20]))))
