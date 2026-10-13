(ns rainbow.math.sets.finset.data-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.finset.data :as finset-data]
            [rainbow.math.sets.finset.range :as finset-range]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint preset-late/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-86 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          finset-range/extend-environment
          finset-data/extend-environment))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest computational-finset-definitions-are-axiom-free-data
  (let [checked-environment @checked-environment
        ids (finset-data/definition-ids checked-environment)]
    (is (= #{'list/no-duplicates 'finset-data/Finset
             'finset-data/enumeration 'finset-data/duplicate-free
             'finset-data/to-set 'finset-data/to-extensional
             'finset-data/card 'list/nat-sum
             'finset-data/sum-nat 'finset-data/range}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration checked-environment id)]
        (is (= :definition (:rainbow/kind declaration)) (str name))
        (is (= :reducible (:rainbow/transparency declaration)) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))
        (is (kernel-checked? checked-environment id) (str name))))))

(deftest exact-enumeration-and-cardinality-laws-are-axiom-free
  (let [checked-environment @checked-environment
        ids (finset-data/theorem-ids checked-environment)]
    (is (= #{'nat/member-range-below
             'list/nat-range-no-duplicates
             'finset-data/enumeration-sound
             'finset-data/enumeration-complete
             'finset-data/sum-nat-enumeration
             'finset-data/card-range}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
