(ns rainbow.math.rational.nnrat.farkas-vector-round-covered-test
  "The coefficient-vector round migrated onto the covering keystone, guarded so a
  keystone regression breaks it LOUDLY.

  farkas-vector-round-covered is one Fourier-Motzkin round whose conclusion
  carries the covering conjunct (via farkas-partition-list-covered), so it is not
  empty-satisfiable. This is the round's existential-vacuity fix and is
  direction-neutral (independent of the uniform-Feasible collapse in
  step/eliminate).

  Guards:
  1. :checked, axiom-free (broken proof -> red);
  2. DEPENDENCY: the proof VALUE mentions farkas-partition-list-covered -- rewire
     off the covered keystone (or lose it) -> RED, no silent weaker fact;
  3. NON-VACUITY: the TYPE references list/length + algebra/nat-add -- revert to
     the vacuous EXISTS-sat-only goal -> RED.

  Tests only; additive (the original farkas-vector-round and the step/eliminate
  wiring are untouched)."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-round-covered :as vrc]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vrc/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- mentions-const? [term id]
  (cond (not (vector? term)) false
        (and (= :const (first term)) (= (second term) id)) true
        :else (boolean (some #(mentions-const? % id) (rest term)))))

(deftest covered-vector-round-holds
  (testing "the covered coefficient-vector round is proved, axiom-free"
    (let [env @checked-environment
          ids (merge (vrc/definition-ids env) (vrc/theorem-ids env))]
      (is (= #{'nnrat/farkas-vector-round-covered} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest covered-vector-round-depends-on-the-covered-keystone
  (testing "the proof VALUE genuinely uses farkas-partition-list-covered -- if
            the keystone stops holding or the proof is rewired off it, RED"
    (let [env @checked-environment
          v (:rainbow/value (environment/declaration
                             env (environment/resolve-id env 'nnrat/farkas-vector-round-covered)))
          keystone-id (environment/resolve-id env 'nnrat/farkas-partition-list-covered)]
      (is (some? keystone-id) "farkas-partition-list-covered not resolvable")
      (is (mentions-const? v keystone-id)
          "farkas-vector-round-covered's PROOF no longer depends on
           farkas-partition-list-covered -- rewired off the covered keystone."))))

(deftest covered-vector-round-type-carries-the-covering
  (testing "the conclusion still carries the covering (list/length + algebra/nat-add)"
    (let [env @checked-environment
          t (:rainbow/type (environment/declaration
                            env (environment/resolve-id env 'nnrat/farkas-vector-round-covered)))
          length-id (environment/resolve-id env 'list/length)
          nat-add-id (environment/resolve-id env 'algebra/nat-add)]
      (is (mentions-const? t length-id)
          "conclusion no longer mentions list/length -- covering stripped, regressed to vacuous")
      (is (mentions-const? t nat-add-id)
          "conclusion no longer mentions algebra/nat-add -- covering stripped, regressed"))))
