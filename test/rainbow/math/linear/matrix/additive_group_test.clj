(ns rainbow.math.linear.matrix.additive-group-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.additive-group :as laws]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (laws/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-matrix-additive-group-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)]
    (is (= #{'matrix/zero-like 'matrix/negate 'matrix/subtract}
           (set (keys definitions))))
    (is (= #{'matrix/zero-like-preserves-same-shape
             'matrix/negate-preserves-same-shape
             'matrix/subtract-preserves-shape
             'matrix/add-zero-like-right
             'matrix/add-zero-like-left
             'matrix/add-negate-right-equivalent-zero-like
             'matrix/add-negate-left-equivalent-zero-like
             'matrix/subtract-self-equivalent-zero-like}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
