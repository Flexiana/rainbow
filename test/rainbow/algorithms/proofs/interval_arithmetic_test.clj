(ns rainbow.algorithms.proofs.interval-arithmetic-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.interval-arithmetic :as interval]
            [rainbow.algorithms.reference.interval-arithmetic :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          interval/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest interval-arithmetic-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (interval/definition-ids checked-environment)
        theorems (interval/theorem-ids checked-environment)]
    (is (= #{'interval/make 'interval/lower 'interval/upper 'interval/add}
           (set (keys definitions))))
    (is (= #{'interval/lower-of-make 'interval/upper-of-make
             'interval/add-bounds 'interval/add-1-3-example
             'interval/add-0-width-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-interval-arithmetic-is-sound
  (is (= [3 7] (executable/add (executable/make 1 3) (executable/make 2 4))))
  (is (= [0 5] (executable/add [0 2] [0 3])))
  (is (= 1 (executable/lower [1 3])))
  (is (= 3 (executable/upper [1 3])))
  ;; Enclosure soundness: any pair of members sums into the summed interval.
  (is (executable/sound-sum? [1 3] [2 4] 2 3))
  (is (executable/sound-sum? [0 2] [0 3] 1 2)))
