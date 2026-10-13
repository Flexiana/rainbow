(ns rainbow.math.finite.markov-contraction-uniqueness-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-contraction-uniqueness :as conditional]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (conditional/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest conditional-uniqueness-is-native-and-axiom-free
  (testing "uniqueness of stationary distributions, conditional on the one
            named contraction inequality carried as an explicit premise --
            the assembly of the congruence, rate-null, and separation
            lemmas, with the Dobrushin step still open and NOT proved here"
    (let [env @checked-environment
          ids (merge (conditional/definition-ids env)
                     (conditional/theorem-ids env))]
      (is (= #{'markov/nnrat-stationary-pointwise-unique-of-proper-contraction}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
