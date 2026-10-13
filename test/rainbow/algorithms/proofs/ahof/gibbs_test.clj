(ns rainbow.algorithms.proofs.ahof.gibbs-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gibbs :as gibbs]
            [rainbow.algorithms.reference.gibbs :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          gibbs/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest gibbs-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (gibbs/definition-ids checked-environment)
        theorems (gibbs/theorem-ids checked-environment)]
    (is (= #{'gibbs/draws?} (set (keys definitions))))
    (is (= #{'gibbs/draws-value 'gibbs/draw-is-from-conditional
             'gibbs/skips-below-draw}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-gibbs-draws-from-conditional
  ;; conditional [2 5 3] -> cdf [2 7 10]
  (is (= [2 7 10] (executable/conditional-cdf [2 5 3])))
  (is (= 1 (executable/draw-index [2 5 3] 5)))
  (is (= 0 (executable/draw-index [2 5 3] 2)))
  (is (= 2 (executable/draw-index [2 5 3] 9))))
