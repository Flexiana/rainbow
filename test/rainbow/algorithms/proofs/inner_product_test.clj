(ns rainbow.algorithms.proofs.inner-product-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.multiply :as signed-mul]
            [rainbow.algorithms.proofs.inner-product :as inner]
            [rainbow.algorithms.reference.inner-product :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          signed-mul/extend-environment
          inner/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest inner-product-is-native-axiom-free
  (let [env @checked-environment
        definitions (inner/definition-ids env)
        theorems (inner/theorem-ids env)]
    (is (= #{'vector/dot} (set (keys definitions))))
    (is (= #{'vector/dot-nil 'vector/dot-example 'vector/dot-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-inner-product-sums-componentwise-products
  (is (= 8 (executable/dot [2 3] [1 2])))
  (is (= 6 (executable/dot [1 2 3] [1 1 1])))
  ;; Orthogonal vectors have zero inner product.
  (is (= 0 (executable/dot [1 0] [0 1])))
  ;; Exact rational components.
  (is (= 5/4 (executable/dot [1/2 1/2] [3/2 1])))
  (is (= 8 (executable/cosine-numerator [2 3] [1 2]))))
