(ns rainbow.algorithms.proofs.ahof.set-cover-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.set-cover :as sc]
            [rainbow.algorithms.reference.set-cover :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          sc/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest set-cover-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (sc/definition-ids checked-environment)
        theorems (sc/theorem-ids checked-environment)]
    (is (= #{'set-cover/greedy-pick} (set (keys definitions))))
    (is (= #{'set-cover/picks-max-coverage 'set-cover/chosen-covers-most-vs-zero
             'set-cover/chosen-covers-most-vs-two}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-set-cover
  (is (= 1 (executable/greedy-pick [2 5 3])))
  (let [chosen (executable/cover #{1 2 3 4 5}
                                 [#{1 2 3} #{2 4} #{3 4 5} #{1}])]
    (is (= #{1 2 3 4 5}
           (reduce into #{} (map [#{1 2 3} #{2 4} #{3 4 5} #{1}] chosen))))))
