(ns rainbow.algorithms.proofs.ahof.articulation-points-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.articulation-points :as ap]
            [rainbow.algorithms.reference.articulation-points :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ap/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest articulation-points-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ap/definition-ids checked-environment)
        theorems (ap/theorem-ids checked-environment)]
    (is (= #{'articulation-points/is-articulation?} (set (keys definitions))))
    (is (= #{'articulation-points/trapped-child-articulation
             'articulation-points/subtree-trapped-below
             'articulation-points/escaping-child-not-articulation}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-articulation-points
  (is (true? (executable/is-articulation? 3 5)))
  (is (false? (executable/is-articulation? 3 1)))
  ;; path 0-1-2-3-4: interior vertices 1,2,3 are articulation points
  (let [adj {0 #{1} 1 #{0 2} 2 #{1 3} 3 #{2 4} 4 #{3}}]
    (is (= #{1 2 3} (executable/articulation-points [0 1 2 3 4] adj))))
  ;; a cycle has no articulation points
  (let [adj {0 #{1 2} 1 #{0 2} 2 #{0 1}}]
    (is (= #{} (executable/articulation-points [0 1 2] adj)))))
