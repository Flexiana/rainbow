(ns rainbow.math.rational.nnrat.farkas-recursion-step-covered-test
  "The first consumer migrated onto the covering-strengthened keystone, with a
  guard that it breaks LOUDLY if the keystone stops holding -- the vacuity
  lesson applied to a consumer.

  Three checks:
  1. farkas-recursion-step-covered is :checked, axiom-free (broken proof -> red);
  2. DEPENDENCY: its proof VALUE mentions farkas-partition-list-covered. If the
     proof were rewired off the covered keystone (e.g. back to the vacuous
     farkas-partition-list-necessary), or the keystone removed, this fails RED --
     the consumer cannot silently fall back to a weaker fact;
  3. NON-VACUITY: its stated TYPE references list/length and algebra/nat-add, so
     the covering conjunct is present in the conclusion; a revert to the vacuous
     EXISTS-sat-only goal strips them and fails RED.

  Tests only; no proved brick edited (covered consumer is additive; the original
  farkas-recursion-step is untouched)."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-recursion-step-covered :as rsc]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (rsc/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- mentions-const? [term id]
  (cond (not (vector? term)) false
        (and (= :const (first term)) (= (second term) id)) true
        :else (boolean (some #(mentions-const? % id) (rest term)))))

(deftest covered-recursion-step-holds
  (testing "the covered recursion step is proved, axiom-free"
    (let [env @checked-environment
          ids (merge (rsc/definition-ids env) (rsc/theorem-ids env))]
      (is (= #{'nnrat/farkas-recursion-step-covered} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest covered-recursion-step-depends-on-the-covered-keystone
  (testing "the proof VALUE genuinely uses farkas-partition-list-covered -- so if
            the keystone stops holding or the proof is rewired off it, this fails
            RED rather than silently proving a weaker fact"
    (let [env @checked-environment
          v (:rainbow/value (environment/declaration
                             env (environment/resolve-id env 'nnrat/farkas-recursion-step-covered)))
          keystone-id (environment/resolve-id env 'nnrat/farkas-partition-list-covered)]
      (is (some? keystone-id) "farkas-partition-list-covered not resolvable")
      (is (mentions-const? v keystone-id)
          "farkas-recursion-step-covered's PROOF no longer depends on
           farkas-partition-list-covered -- it was rewired off the covered
           keystone (or the keystone is gone). It must not fall back silently."))))

(deftest covered-recursion-step-type-carries-the-covering
  (testing "the conclusion still carries the covering (list/length + algebra/nat-add);
            a revert to the vacuous EXISTS-sat-only goal fails RED"
    (let [env @checked-environment
          t (:rainbow/type (environment/declaration
                            env (environment/resolve-id env 'nnrat/farkas-recursion-step-covered)))
          length-id (environment/resolve-id env 'list/length)
          nat-add-id (environment/resolve-id env 'algebra/nat-add)]
      (is (mentions-const? t length-id)
          "conclusion no longer mentions list/length -- covering stripped, regressed to vacuous")
      (is (mentions-const? t nat-add-id)
          "conclusion no longer mentions algebra/nat-add -- covering stripped, regressed"))))
