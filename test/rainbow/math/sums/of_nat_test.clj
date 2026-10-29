(ns rainbow.math.sums.of-nat-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s]
            [rainbow.math.sums.of-nat :as m]
            [rainbow.or.lp-certificate :as literals]))

(def checked-environment
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "Checkpoint rejected" {})))
           (m/extend-environment (:environment cp)))))
(defn- core! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- nn [k] (nth (iterate s/succ s/nz) k))
(defn- lit [n] (#'literals/signed-literal n))

(deftest all-of-nat-declarations-check-with-empty-axiom-closures
  (let [env @checked-environment ids (m/theorem-ids env)]
    (is (= 3 (count ids)))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)
            r (kernel/check env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d)))
            axioms (kernel/axioms env id)]
        (println name (:status r) :axioms axioms)
        (is (= :checked (:status r)) (str name))
        (is (= #{} axioms) (str name))))))

(deftest the-constant-sum-instantiates-and-a-wrong-count-is-rejected
  ;; sum of three 5s ~ 5 * of-nat 3 checks; the same proof does not prove ~ 5 * of-nat 2.
  (let [env @checked-environment
        proof (s/call 'signed/expr-sum-constant-of-nat (lit 5) (nn 3))
        C (f/lam [['ci s/nat]] (lit 5))
        ok (kernel/check env (core! env proof) (core! env (s/eqv (s/sum C (nn 3)) (s/mul (lit 5) (m/of-nat (nn 3))))) #{})
        bad (kernel/check env (core! env proof) (core! env (s/eqv (s/sum C (nn 3)) (s/mul (lit 5) (m/of-nat (nn 2))))) #{})]
    (println :of-nat-control :three (:status ok) :two (:status bad) (get-in bad [:error :error/category]))
    (is (= :checked (:status ok)))
    (is (= :rejected (:status bad)))
    (is (= :kernel/type-mismatch (get-in bad [:error :error/category])))))
