(ns rainbow.algorithms.proofs.hooke-jeeves-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.hooke-jeeves :as hooke]
            [rainbow.algorithms.reference.hooke-jeeves :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          hooke/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest hooke-jeeves-moves-are-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (hooke/definition-ids checked-environment)
        theorems (hooke/theorem-ids checked-environment)]
    (is (= #{'hooke/probe 'hooke/pattern-move} (set (keys definitions))))
    (is (= #{'hooke/probe-unfold 'hooke/pattern-move-unfold
             'hooke/probe-example 'hooke/pattern-move-example
             'hooke/pattern-move-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-hooke-jeeves-probes-and-accelerates-exactly
  ;; Exploratory probe.
  (is (= [1 2] (executable/probe [0 0] [1 2])))
  (is (= [3 5] (executable/probe [1 2] [2 3])))
  ;; Pattern (acceleration) move extrapolates past the improved point.
  (is (= [2 4] (executable/pattern-move [0 0] [1 2])))
  (is (= [2 4 6] (executable/pattern-move [0 0 0] [1 2 3])))
  ;; A real non-origin acceleration: base [1,1], improved [2,3] -> [3,5].
  (is (= [3 5] (executable/pattern-move [1 1] [2 3])))
  ;; Acceptance keeps a probe only when it improves.
  (let [objective (fn [[a b]] (+ (* a a) (* b b)))]
    (is (= [0 0] (executable/accept objective [1 1] [0 0])))
    (is (= [1 1] (executable/accept objective [1 1] [3 3])))))
