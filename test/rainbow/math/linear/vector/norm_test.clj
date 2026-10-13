(ns rainbow.math.linear.vector.norm-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.multiply :as signed-mul]
            [rainbow.algorithms.proofs.inner-product :as inner]
            [rainbow.math.linear.vector.norm :as norm]
            [rainbow.algorithms.reference.vector-norm :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          signed-mul/extend-environment
          inner/extend-environment
          norm/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest vector-norm-is-native-axiom-free
  (let [env @checked-environment
        definitions (norm/definition-ids env)
        theorems (norm/theorem-ids env)]
    (is (= #{'norm/norm-squared 'norm/is-norm} (set (keys definitions))))
    (is (= #{'norm/norm-squared-example 'norm/norm-example
             'norm/unit-norm-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-vector-norm-computes-exactly
  (is (= 25 (executable/norm-squared [3 4])))
  (is (= 5 (executable/norm [3 4])))
  (is (= 1 (executable/norm [1 0 0])))
  (is (= 1 (executable/cosine-similarity [3 4] [3 4])))
  (is (= 0 (executable/cosine-similarity [3 0] [0 4]))))
