(ns rainbow.math.rational.nnrat.farkas-vector-step-covered-test
  "The covered elimination step, guarded so a keystone-chain regression breaks
  it RED. farkas-vector-step-covered's held-goal carries the covering conjunct
  (threaded from round-covered through unit-column via repr length-preservation),
  so it is not empty-satisfiable. Direction-neutral (does not touch the Feasible
  uniformity / Option 1/2).

  Guards: (1) :checked, axiom-free; (2) DEPENDENCY -- the proof VALUE mentions
  farkas-vector-round-covered (rewire off the covered chain -> RED); (3)
  NON-VACUITY -- the TYPE references list/length + algebra/nat-add (revert to the
  vacuous EXISTS-held-only goal -> RED). Tests only; additive."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-step-covered :as sc]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (sc/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- mentions-const? [term id]
  (cond (not (vector? term)) false
        (and (= :const (first term)) (= (second term) id)) true
        :else (boolean (some #(mentions-const? % id) (rest term)))))

(deftest covered-step-holds
  (testing "the covered step is proved, axiom-free"
    (let [env @checked-environment
          ids (merge (sc/definition-ids env) (sc/theorem-ids env))]
      (is (= #{'nnrat/farkas-vector-step-covered} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest covered-step-depends-on-round-covered
  (testing "the proof VALUE uses farkas-vector-round-covered -- rewire off the
            covered chain -> RED"
    (let [env @checked-environment
          v (:rainbow/value (environment/declaration
                            env (environment/resolve-id env 'nnrat/farkas-vector-step-covered)))
          rc-id (environment/resolve-id env 'nnrat/farkas-vector-round-covered)]
      (is (some? rc-id) "farkas-vector-round-covered not resolvable")
      (is (mentions-const? v rc-id)
          "farkas-vector-step-covered no longer depends on farkas-vector-round-covered"))))

(deftest covered-step-type-carries-the-covering
  (testing "the held-goal still carries the covering (list/length + algebra/nat-add)"
    (let [env @checked-environment
          t (:rainbow/type (environment/declaration
                            env (environment/resolve-id env 'nnrat/farkas-vector-step-covered)))]
      (is (mentions-const? t (environment/resolve-id env 'list/length))
          "held-goal no longer mentions list/length -- covering stripped")
      (is (mentions-const? t (environment/resolve-id env 'algebra/nat-add))
          "held-goal no longer mentions algebra/nat-add -- covering stripped"))))
