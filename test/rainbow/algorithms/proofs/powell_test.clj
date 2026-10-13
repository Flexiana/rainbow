(ns rainbow.algorithms.proofs.powell-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.powell :as powell]
            [rainbow.algorithms.reference.powell :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint) vector/extend-environment
          powell/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest powell-net-direction-is-native-axiom-free
  (let [env @checked-environment
        definitions (powell/definition-ids env)
        theorems (powell/theorem-ids env)]
    (is (= #{'powell/net-direction} (set (keys definitions))))
    (is (= #{'powell/net-direction-unfold 'powell/net-direction-example
             'powell/net-direction-3d-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-powell-generates-conjugate-directions-exactly
  (is (= [2 3] (executable/net-direction [0 0] [2 3])))
  (is (= [1 2 3] (executable/net-direction [0 0 0] [1 2 3])))
  ;; Real non-origin cycle: from [1,1] to [4,5] the net direction is [3,4].
  (is (= [3 4] (executable/net-direction [1 1] [4 5])))
  ;; Direction-set rotation drops the oldest and appends the new one.
  (is (= [[0 1] [1 0] [3 4]]
         (executable/rotate-directions [[1 0] [0 1] [1 0]] [3 4]))))
