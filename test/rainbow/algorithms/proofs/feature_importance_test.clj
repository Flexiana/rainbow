(ns rainbow.algorithms.proofs.feature-importance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.feature-importance :as fi]
            [rainbow.algorithms.reference.feature-importance :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (fi/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest feature-importance-is-native-axiom-free
  (let [env @checked-environment
        definitions (fi/definition-ids env)
        theorems (fi/theorem-ids env)]
    (is (= #{'importance/importance} (set (keys definitions))))
    (is (= #{'importance/importance-unfold 'importance/relied-on-example
             'importance/unused-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-feature-importance-measures-score-drop
  (is (= 2 (executable/importance 5 3)))
  (is (= 0 (executable/importance 4 4)))
  ;; A harmful feature increases the score when kept: negative importance.
  (is (= -1 (executable/importance 3 4)))
  ;; Mean importance over repeated permutations.
  (is (= 2 (executable/mean-importance 5 [4 3 2]))))
