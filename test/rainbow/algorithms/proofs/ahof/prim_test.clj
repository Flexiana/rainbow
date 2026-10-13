(ns rainbow.algorithms.proofs.ahof.prim-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.prim :as prim]
            [rainbow.algorithms.reference.prim :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          prim/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest prim-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (prim/definition-ids checked-environment)
        theorems (prim/theorem-ids checked-environment)]
    (is (= #{'prim/lighter-edge} (set (keys definitions))))
    (is (= #{'prim/picks-lighter-crossing 'prim/picks-second-when-lighter
             'prim/chosen-edge-is-minimum}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-prim
  (is (= 2 (executable/lighter-edge 1 2 4 5)))
  (is (= 5 (executable/lighter-edge 6 2 3 5)))
  ;; triangle 0-1=1, 1-2=2, 0-2=3 : MST weight 1+2=3
  (is (= 3 (executable/mst-weight 3 {[0 1] 1 [1 0] 1 [1 2] 2 [2 1] 2
                                     [0 2] 3 [2 0] 3}))))
