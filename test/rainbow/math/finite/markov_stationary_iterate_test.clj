(ns rainbow.math.finite.markov-stationary-iterate-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-stationary-iterate :as fixed]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (fixed/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest stationary-iterate-fixed-integrates-with-the-markov-chain-world
  (testing "one environment carries the whole chain -- stationarity, kernel
            composition, the iterate laws, and the new fixed-point theorem --
            replayed from the D63 checkpoint, with the composed upstream
            lemmas the proof consumes resolving in the same world"
    (let [env @checked-environment
          ids (merge (fixed/definition-ids env) (fixed/theorem-ids env))]
      (is (= #{'markov/nnrat-stationary-iterate-fixed} (set (keys ids))))
      ;; The exact lemmas the induction composes must live in this same
      ;; environment; a chain regression upstream fails here, not just in
      ;; the upstream module's own test.
      (doseq [dependency '[markov/nnrat-kernel-iterate-successor
                           markov/nnrat-kernel-step-respects-mass-equivalence
                           markov/nnrat-stationary
                           markov/nnrat-kernel-iterate]]
        (is (some? (environment/resolve-id env dependency)) (str dependency)))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
