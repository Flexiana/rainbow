(ns rainbow.algorithms.proofs.ahof.beam-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.beam-search :as beam]
            [rainbow.algorithms.reference.beam-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          beam/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest beam-search-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (beam/definition-ids checked-environment)
        theorems (beam/theorem-ids checked-environment)]
    (is (= #{'beam-search/in-beam?} (set (keys definitions))))
    (is (= #{'beam-search/keeps-high-scorer 'beam-search/retained-meets-cutoff
             'beam-search/prunes-low-scorer}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-beam-search
  (is (true? (executable/in-beam? 7 5)))
  (is (false? (executable/in-beam? 3 5)))
  (is (= [[:b 9] [:a 7]] (executable/beam 2 [[:a 7] [:b 9] [:c 2] [:d 5]]))))
