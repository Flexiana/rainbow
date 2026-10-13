(ns rainbow.algorithms.proofs.box-projection-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.box-projection :as projection]
            [rainbow.algorithms.reference.box-projection :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          projection/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest box-projection-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (projection/definition-ids checked-environment)
        theorems (projection/theorem-ids checked-environment)]
    (is (= #{'projection/clamp} (set (keys definitions))))
    (is (= #{'projection/clamp-inside 'projection/clamp-above
             'projection/clamp-below 'projection/clamp-below-hi
             'projection/clamp-above-lo}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-box-projection-is-feasible
  (is (= 5 (executable/clamp 2 8 5)))
  (is (= 8 (executable/clamp 2 8 10)))
  (is (= 2 (executable/clamp 2 8 1)))
  ;; A projected step from x=7 with a large descent still lands in the box.
  (let [x* (executable/projected-step 2 8 7 100 1)]
    (is (executable/feasible? 2 8 x*))
    (is (= 2 x*)))
  ;; Projection is idempotent: projecting an already-feasible point is identity.
  (is (= 5 (executable/clamp 2 8 (executable/clamp 2 8 5)))))
