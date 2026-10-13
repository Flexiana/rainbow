(ns rainbow.algorithms.proofs.edit-distance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.edit-distance :as edit-distance]
            [rainbow.algorithms.reference.edit-distance :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          edit-distance/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest edit-distance-cell-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (edit-distance/definition-ids checked-environment)
        theorems (edit-distance/theorem-ids checked-environment)]
    (is (= #{'edit-distance/cell} (set (keys definitions))))
    (is (= #{'edit-distance/cell-example
             'edit-distance/cell-below-delete
             'edit-distance/cell-below-insert
             'edit-distance/cell-below-substitute}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-edit-distance-matches
  (is (= 2 (executable/cell 3 5 2)))
  ;; kitten -> sitting is the classic edit distance 3.
  (is (= 3 (executable/distance "kitten" "sitting")))
  ;; identical sequences need no edits; disjoint single chars need one.
  (is (= 0 (executable/distance "abc" "abc")))
  (is (= 1 (executable/distance "a" "b")))
  (is (= 3 (executable/distance "" "cat"))))
