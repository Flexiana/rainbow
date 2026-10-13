(ns rainbow.math.finite.set-classical-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.finite.set-classical :as classical]))

(deftest classical-finite-transport-is-explicit-kernel-checked-proof-data
  (let [checkpoint (checkpoint/load-checkpoint
                    "artifacts/day69/checkpoint.edn.gz")
        constructive (finite-set/extend-environment
                      (:environment checkpoint))
        checked (classical/extend-environment constructive)
        excluded-middle-id
        (environment/resolve-id checked 'logic/excluded-middle)
        ids (classical/theorem-ids checked)]
    (is (= :replayed (:status checkpoint)))
    (is (= 11 (count ids)))
    (doseq [[alias id] ids]
      (let [declaration (environment/declaration checked id)
            replay (kernel/check checked
                                 (:rainbow/value declaration)
                                 (:rainbow/type declaration)
                                 (set (:rainbow/universes declaration)))]
        (is (= :theorem (:rainbow/kind declaration)) (str alias))
        (is (= :checked (:status replay)) (str alias))
        (is (= #{excluded-middle-id} (kernel/axioms checked id))
            (str alias))))))
