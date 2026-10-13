(ns rainbow.algorithms.proofs.ahof.pagerank-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.pagerank :as pagerank]
            [rainbow.algorithms.reference.pagerank :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          pagerank/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest pagerank-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (pagerank/definition-ids checked-environment)
        theorems (pagerank/theorem-ids checked-environment)]
    (is (= #{'pagerank/update} (set (keys definitions))))
    (is (= #{'pagerank/update-example 'pagerank/dangling-keeps-teleport}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-pagerank
  (is (= 3/4 (executable/pagerank-update 1/4 1/2 1)))
  (is (= 1/4 (executable/pagerank-update 1/4 1/2 0)))
  ;; 0<->1 mutual links, symmetric graph -> equal ranks summing to 1
  (let [pr (executable/pagerank 2 {0 [1] 1 [0]} 1/2 20)]
    (is (= (pr 0) (pr 1)))
    (is (= 1 (reduce + pr)))))
