(ns rainbow.math.finite.vector-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.reference.finite-vector :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vector/extend-environment (:environment checkpoint)))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-vectors-are-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (vector/definition-ids checked-environment)
        theorems (vector/theorem-ids checked-environment)]
    (is (= #{'vector/scale 'vector/negate 'vector/add 'vector/subtract}
           (set (keys definitions))))
    (is (= #{'vector/add-nil 'vector/subtract-unfold 'vector/add-example
             'vector/scale-example 'vector/add-example-3d}
           (set (keys theorems))))
    ;; General n-dimensional vector operations, axiom-free -- the first genuinely
    ;; multi-dimensional state in the corpus.
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-vectors-add-scale-and-subtract-elementwise
  ;; Elementwise addition, scalar scaling, and subtraction over exact rationals.
  (is (= [4 6] (executable/add [1 2] [3 4])))
  (is (= [4 6 8] (executable/add [1 2 3] [3 4 5])))
  (is (= [2 4] (executable/scale 2 [1 2])))
  (is (= [-1 -2] (executable/negate [1 2])))
  (is (= [3 4] (executable/subtract [4 6] [1 2])))
  ;; Exact rational components, not floats.
  (is (= [3/4 5/4] (executable/add [1/2 1/2] [1/4 3/4]))))
