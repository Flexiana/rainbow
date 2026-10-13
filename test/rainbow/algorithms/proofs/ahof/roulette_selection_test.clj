(ns rainbow.algorithms.proofs.ahof.roulette-selection-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.roulette-selection :as roulette]
            [rainbow.algorithms.reference.roulette-selection :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          roulette/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest roulette-selection-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (roulette/definition-ids checked-environment)
        theorems (roulette/theorem-ids checked-environment)]
    (is (= #{'roulette/lands?} (set (keys definitions))))
    (is (= #{'roulette/lands-on-individual 'roulette/landing-is-valid
             'roulette/passes-over-below-spin}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-roulette-spins-the-wheel
  ;; fitnesses [3 4 2] -> wheel [3 7 9]
  (is (= [3 7 9] (executable/wheel [3 4 2])))
  ;; a spin of 6 lands on index 1 (cumulative reaches 7 >= 6)
  (is (= 1 (executable/select-index [3 4 2] 6)))
  ;; a spin of 3 lands on index 0
  (is (= 0 (executable/select-index [3 4 2] 3)))
  ;; a spin of 8 lands on index 2
  (is (= 2 (executable/select-index [3 4 2] 8))))
