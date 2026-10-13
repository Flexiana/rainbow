(ns rainbow.algorithms.proofs.ahof.neural-vf-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.neural-vf :as neural]
            [rainbow.algorithms.reference.neural-vf :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          neural/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest neural-vf-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (neural/definition-ids checked-environment)
        theorems (neural/theorem-ids checked-environment)]
    (is (= #{'neural-vf/neuron} (set (keys definitions))))
    (is (= #{'neural-vf/neuron-unfold
             'neural-vf/neuron-example
             'neural-vf/neuron-above-bias}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-neural-vf-forward-pass
  (is (= 15 (executable/neuron 2 3 1 4 5)))
  (is (= 0 (executable/relu -3)))
  (is (= 4 (executable/relu 4)))
  ;; A 2-neuron ReLU layer; the second neuron's negative pre-activation clamps.
  (is (= [15 0]
         (executable/layer [[2 1] [-5 0]] [5 1] [3 4]))))
