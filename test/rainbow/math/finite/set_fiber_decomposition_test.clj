(ns rainbow.math.finite.set-fiber-decomposition-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set-fiber-decomposition :as decomposition]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (decomposition/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-sources-decompose-constructively-into-finite-fibers
  (let [checked-environment @checked-environment
        definitions (decomposition/definition-ids checked-environment)
        theorems (decomposition/theorem-ids checked-environment)]
    (is (empty? definitions))
    (is (= #{'set/source-subset-image-fiber-union
             'set/image-fiber-union-subset-source
             'set/image-fiber-union-decomposition
             'set/finite-image-fiber-union}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
