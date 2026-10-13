(ns rainbow.algorithms.proofs.ahof.cosine-similarity-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.cosine-similarity :as cosine]
            [rainbow.algorithms.reference.cosine-similarity :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          cosine/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest cosine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (cosine/definition-ids checked-environment)
        theorems (cosine/theorem-ids checked-environment)]
    (is (= #{'cosine/similarity} (set (keys definitions))))
    (is (= #{'cosine/cosine-example 'cosine/aligned-vectors-cosine-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-cosine
  (is (= 3/4 (executable/cosine 3 4)))
  (is (= 1 (executable/cosine 5 5)))
  ;; parallel vectors -> cosine 1
  (is (< (abs (- 1.0 (executable/similarity [1 2 3] [2 4 6]))) 1e-9))
  ;; orthogonal vectors -> cosine 0
  (is (< (abs (executable/similarity [1 0] [0 1])) 1e-9)))
