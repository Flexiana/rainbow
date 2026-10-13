(ns rainbow.algorithms.proofs.ahof.union-by-rank-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.union-by-rank :as ubr]
            [rainbow.algorithms.reference.union-by-rank :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ubr/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest union-by-rank-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ubr/definition-ids checked-environment)
        theorems (ubr/theorem-ids checked-environment)]
    (is (= #{'union-by-rank/attach-under?} (set (keys definitions))))
    (is (= #{'union-by-rank/lower-rank-attached-under
             'union-by-rank/attached-rank-at-most
             'union-by-rank/higher-rank-becomes-parent}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-union-by-rank
  (is (true? (executable/attach-under? 2 4)))
  (is (false? (executable/attach-under? 5 3)))
  (let [uf (-> (executable/make-uf 6)
               (executable/union 0 1)
               (executable/union 1 2)
               (executable/union 3 4))]
    (is (executable/connected? uf 0 2))
    (is (not (executable/connected? uf 0 3)))
    (is (executable/connected? uf 3 4))))
