(ns rainbow.algorithms.proofs.firefly-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.firefly :as firefly]
            [rainbow.algorithms.reference.firefly :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          firefly/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest firefly-attraction-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (firefly/definition-ids checked-environment)
        theorems (firefly/theorem-ids checked-environment)]
    (is (= #{'firefly/attraction-step} (set (keys definitions))))
    (is (= #{'firefly/attraction-unfold
             'firefly/full-attraction-example
             'firefly/full-attraction-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-firefly-moves-toward-brighter-exactly
  ;; Full attraction (beta = 1) lands on the brighter firefly.
  (is (= [3 2] (executable/attraction-step [0 0] [3 2] 1)))
  (is (= [2 4 6] (executable/attraction-step [0 0 0] [2 4 6] 1)))
  ;; Half attraction with a real (nonzero-origin) separation: [2,2] moving
  ;; toward [6,6] by 1/2 lands at the midpoint [4,4].
  (is (= [4 4] (executable/attraction-step [2 2] [6 6] 1/2)))
  ;; brighter? uses the lower-objective convention.
  (is (true? (executable/brighter? (fn [[a b]] (+ (* a a) (* b b))) [0 0] [3 4])))
  ;; Move only happens toward a genuinely brighter firefly.
  (let [objective (fn [[a b]] (+ (* a a) (* b b)))]
    (is (= [1 1] (executable/move-toward-brighter objective [2 2] [0 0] 1/2)))
    (is (= [3 3] (executable/move-toward-brighter objective [3 3] [9 9] 1/2)))))
