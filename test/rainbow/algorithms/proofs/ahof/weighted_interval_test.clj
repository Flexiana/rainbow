(ns rainbow.algorithms.proofs.ahof.weighted-interval-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.weighted-interval :as wi]
            [rainbow.algorithms.reference.weighted-interval :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          wi/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest weighted-interval-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (wi/definition-ids checked-environment)
        theorems (wi/theorem-ids checked-environment)]
    (is (= #{'weighted-interval/cell} (set (keys definitions))))
    (is (= #{'weighted-interval/includes-when-better
             'weighted-interval/excludes-when-better
             'weighted-interval/dominates-include
             'weighted-interval/dominates-exclude}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-weighted-interval
  (is (= 7 (executable/cell 7 5)))
  (is (= 8 (executable/cell 4 8)))
  ;; [1 3 5][2 5 6][4 6 5][6 7 4]: best is [1 3 5]+[4 6 5]+[6 7 4]=14
  (is (= 14 (executable/max-weight [[1 3 5] [2 5 6] [4 6 5] [6 7 4]]))))
