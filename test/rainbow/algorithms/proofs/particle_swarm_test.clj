(ns rainbow.algorithms.proofs.particle-swarm-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.particle-swarm :as swarm]
            [rainbow.algorithms.reference.particle-swarm :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          swarm/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest particle-swarm-update-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (swarm/definition-ids checked-environment)
        theorems (swarm/theorem-ids checked-environment)]
    (is (= #{'swarm/velocity-update 'swarm/position-update 'swarm/step}
           (set (keys definitions))))
    (is (= #{'swarm/position-update-unfold 'swarm/step-unfold
             'swarm/velocity-update-example 'swarm/position-update-example
             'swarm/step-example}
           (set (keys theorems))))
    ;; The first optimizer over genuinely vector-valued state, axiom-free.
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-particle-swarm-updates-vector-state-exactly
  ;; Unit weights, particle at the origin, velocity [1,0], personal best [2,0],
  ;; global best [0,2]: v' = [1,0]+[2,0]+[0,2] = [3,2], x' = [0,0]+[3,2] = [3,2].
  (is (= [3 2] (executable/velocity-update 1 1 1 [1 0] [0 0] [2 0] [0 2])))
  (is (= [3 2] (executable/position-update [0 0] [3 2])))
  (is (= [[3 2] [3 2]]
         (executable/step 1 1 1 [1 0] [0 0] [2 0] [0 2])))
  ;; Non-origin particle exercises real subtraction of both bests.
  (is (= [3/2 3/2]
         (executable/velocity-update 1/2 1 1 [1 1] [1 1] [2 2] [1 1])))
  ;; The global-best REDUCE selects the minimum-objective position.
  (is (= [0 2]
         (executable/global-best (fn [[a b]] (+ (* a a) (* (- b 2) (- b 2))))
                                 [[3 2] [0 2] [1 1]]))))
