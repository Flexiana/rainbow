(ns rainbow.algorithms.proofs.cross-validation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.cross-validation :as ahof-v4]
            [rainbow.algorithms.proofs.cross-validation :as iteration]
            [rainbow.algorithms.reference.cross-validation :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o35-pattern-search/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O35 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-v4/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest cross-validation-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'validation/cross-validation-total
             'validation/cross-validation-mean}
           (set (keys definitions))))
    (is (= #{'validation/cross-validation-total-unfold
             'validation/cross-validation-mean-unfold}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-v4-cross-validation-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-v4/theorem-ids checked-environment)]
    (is (= #{'ahof-v4/total-is-one 'ahof-v4/mean-is-one-half
             'ahof-v4/cross-validation}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-cross-validation-averages-the-folds
  ;; Two folds scored 3/4 and 1/4: total 1, over count 2 gives the mean 1/2.
  (is (= 1 (executable/total [3/4 1/4])))
  (is (= 1/2 (executable/mean [3/4 1/4] 2)))
  ;; Three equal folds average to their common score.
  (is (= 1/2 (executable/mean [1/2 1/2 1/2] 3)))
  (is (= 1/3 (executable/mean [1 0 0] 3))))
