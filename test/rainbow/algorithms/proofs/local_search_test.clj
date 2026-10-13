(ns rainbow.algorithms.proofs.local-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.local-search :as ahof-d40]
            [rainbow.algorithms.proofs.local-search :as iteration]
            [rainbow.algorithms.reference.local-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d2-exact-inference/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D2 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d40/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest local-search-engine-is-native-axiom-free-and-reusable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'search/nnrat-best-neighbor 'search/nnrat-hill-climb}
           (set (keys definitions))))
    (is (= #{'search/nnrat-best-neighbor-is-candidate
             'search/nnrat-best-neighbor-improves
             'search/nnrat-hill-climb-zero
             'search/nnrat-hill-climb-successor
             'search/nnrat-best-neighbor-transfer}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d40-search-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d40/theorem-ids checked-environment)]
    (is (= #{'ahof-d40/best-is-one
             'ahof-d40/admissible
             'ahof-d40/improvement
             'ahof-d40/hill-climb-recurrence
             'ahof-d40/local-search}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-reference-hill-climbs-exactly
  (let [candidates [0 1 2]
        objective (fn [p] (case p 1 3/4 2 1/2 1/4))]
    (is (= 1 (executable/best-neighbor candidates objective 0)))
    (is (= 1 (executable/hill-climb candidates objective 3 0)))
    ;; The objective never decreases from the current point.
    (is (<= (objective 0)
            (objective (executable/best-neighbor candidates objective 0))))))
