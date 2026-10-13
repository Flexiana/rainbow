(ns rainbow.algorithms.proofs.ahof.dual-simplex-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.dual-simplex :as dual]
            [rainbow.algorithms.reference.dual-simplex :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          dual/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest dual-simplex-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (dual/definition-ids checked-environment)
        theorems (dual/theorem-ids checked-environment)]
    (is (= #{'dual-simplex/choose-entering} (set (keys definitions))))
    (is (= #{'dual-simplex/enters-min-ratio-column
             'dual-simplex/enters-first-when-smaller
             'dual-simplex/chosen-ratio-is-minimal}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-dual-simplex-ratio-test
  (is (= 1 (executable/choose-entering 3/2 0 1/2 1)))
  (is (= 0 (executable/choose-entering 1/4 0 1 1)))
  (is (= 2 (executable/ratio-test [[3/2 0] [1 1] [1/2 2]]))))
