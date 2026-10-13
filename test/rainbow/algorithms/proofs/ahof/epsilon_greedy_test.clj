(ns rainbow.algorithms.proofs.ahof.epsilon-greedy-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.epsilon-greedy :as eps]
            [rainbow.algorithms.reference.epsilon-greedy :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          eps/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest epsilon-greedy-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (eps/definition-ids checked-environment)
        theorems (eps/theorem-ids checked-environment)]
    (is (= #{'epsilon-greedy/explores? 'epsilon-greedy/exploit-action}
           (set (keys definitions))))
    (is (= #{'epsilon-greedy/draw-explores 'epsilon-greedy/exploration-in-band
             'epsilon-greedy/draw-exploits 'epsilon-greedy/exploit-is-greedy}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-epsilon-greedy-selects
  (is (true? (executable/explores? 1/10 1/4)))
  (is (false? (executable/explores? 1/2 1/4)))
  (is (= 1 (executable/exploit-action [5 7 4])))
  ;; exploit branch (u=1/2 > eps): greedy action 1
  (is (= 1 (executable/select-action [5 7 4] 1/4 1/2 99)))
  ;; explore branch (u=1/10 <= eps): random action 99
  (is (= 99 (executable/select-action [5 7 4] 1/4 1/10 99))))
