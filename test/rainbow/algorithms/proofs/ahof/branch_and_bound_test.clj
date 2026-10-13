(ns rainbow.algorithms.proofs.ahof.branch-and-bound-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.branch-and-bound :as specialization]
            [rainbow.algorithms.proofs.branch-and-bound :as iteration]
            [rainbow.algorithms.reference.branch-and-bound :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          specialization/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

;; D34 reuses the shared branch-and-bound/* lemma; check the D34-specific
;; specialization declarations are native and axiom-free.
(deftest branch-and-bound-specialization-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (specialization/definition-ids env)
                   (specialization/theorem-ids env))]
    (is (= #{'ahof-d34/prunes-weak-node 'ahof-d34/pruning-sound
             'ahof-d34/explores-strong-node 'ahof-d34/branch-and-bound}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-branch-and-bound-matches-worked-instance
  ;; maximization convention: dominated when bound <= incumbent
  (is (true? (executable/dominated? 2 8)))
  (is (false? (executable/dominated? 9 8))))
