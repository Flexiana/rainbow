(ns rainbow.algorithms.proofs.ahof.adaboost-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.adaboost :as ada]
            [rainbow.algorithms.reference.adaboost :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ada/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest adaboost-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ada/definition-ids checked-environment)
        theorems (ada/theorem-ids checked-environment)]
    (is (= #{'adaboost/earns-more-weight?} (set (keys definitions))))
    (is (= #{'adaboost/lower-error-earns-more
             'adaboost/more-weight-means-lower-error
             'adaboost/higher-error-earns-less}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-adaboost
  (is (true? (executable/earns-more-weight? 1/4 1/2)))
  (is (false? (executable/earns-more-weight? 1/2 1/4)))
  ;; a low-error learner (err 1/10) voting +1 outweighs a high-error one (err
  ;; 2/5) voting -1
  (is (= 1 (executable/strong-vote [1/10 2/5] [1 -1]))))
