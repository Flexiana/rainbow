(ns rainbow.math.sets.finset.filter-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.finset.filter :as finset-filter]
            [rainbow.math.sets.finset.range :as finset-range]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint preset-late/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-86 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          finset-range/extend-environment
          finset-filter/extend-environment))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest certified-filter-definitions-are-axiom-free
  (let [checked-environment @checked-environment
        ids (finset-filter/definition-ids checked-environment)]
    (is (= #{'decision/DecidablePred 'finset/filter} (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest filter-false-has-only-extensional-finset-axioms
  (let [checked-environment @checked-environment
        id (get (finset-filter/theorem-ids checked-environment)
                'finset/filter-false)
        expected
        (set (map #(environment/resolve-id checked-environment %)
                  ['logic/proof-irrelevance
                   'logic/function-extensionality
                   'logic/proposition-extensionality]))]
    (is (= expected (kernel/axioms checked-environment id)))
    (is (kernel-checked? checked-environment id))))
