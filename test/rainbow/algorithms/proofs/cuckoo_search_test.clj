(ns rainbow.algorithms.proofs.cuckoo-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.cuckoo-search :as cuckoo]
            [rainbow.algorithms.reference.cuckoo-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint) vector/extend-environment
          cuckoo/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest cuckoo-levy-step-is-native-axiom-free
  (let [env @checked-environment
        definitions (cuckoo/definition-ids env)
        theorems (cuckoo/theorem-ids env)]
    (is (= #{'cuckoo/levy-step} (set (keys definitions))))
    (is (= #{'cuckoo/levy-step-unfold 'cuckoo/levy-step-example
             'cuckoo/scaled-flight-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-cuckoo-flies-and-abandons-exactly
  (is (= [3 2] (executable/levy-step [0 0] 1 [3 2])))
  (is (= [2 4] (executable/levy-step [0 0] 2 [1 2])))
  ;; A flight from a non-origin nest: [1,1] + 1/2*[4,2] = [3,2].
  (is (= [3 2] (executable/levy-step [1 1] 1/2 [4 2])))
  ;; Abandon keeps the better nest.
  (let [obj (fn [[a b]] (+ (* a a) (* b b)))]
    (is (= [0 0] (executable/abandon obj [1 1] [0 0])))
    (is (= [1 1] (executable/abandon obj [1 1] [3 3])))))
