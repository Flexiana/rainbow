(ns rainbow.algorithms.proofs.ahof.pc-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.pc :as pc]
            [rainbow.algorithms.reference.pc :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          pc/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest pc-independence-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (pc/definition-ids checked-environment)
        theorems (pc/theorem-ids checked-environment)]
    (is (= #{'pc/independent?} (set (keys definitions))))
    (is (= #{'pc/declares-independence 'pc/independence-is-sound
             'pc/keeps-dependent-edge}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-pc-prunes-independent-edges
  (is (true? (executable/independent? 2 5)))
  (is (false? (executable/independent? 8 5)))
  ;; Edges with statistics {AB 8, AC 2, BC 9}: the independent A-C is removed.
  (let [stat {[:a :b] 8, [:a :c] 2, [:b :c] 9}]
    (is (= [[:a :b] [:b :c]] (executable/skeleton [[:a :b] [:a :c] [:b :c]] stat 5)))))
