(ns rainbow.algorithms.proofs.full-factorial-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.full-factorial :as full-factorial]
            [rainbow.algorithms.reference.full-factorial :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          full-factorial/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest full-factorial-design-size-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (full-factorial/definition-ids checked-environment)
        theorems (full-factorial/theorem-ids checked-environment)]
    (is (= #{'full-factorial/design-size} (set (keys definitions))))
    (is (= #{'full-factorial/design-size-unfold
             'full-factorial/design-size-2x3-example
             'full-factorial/design-size-2x3x2-example
             'full-factorial/design-size-empty-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-full-factorial-matches-the-count
  (is (= 6 (executable/design-size [2 3])))
  (is (= 12 (executable/design-size [2 3 2])))
  (is (= 1 (executable/design-size [])))
  ;; The enumeration realizes exactly design-size distinct points.
  (is (= 6 (count (executable/cartesian-product [[0 1] [0 1 2]]))))
  (is (= 12 (count (executable/cartesian-product [[0 1] [0 1 2] [0 1]])))))
