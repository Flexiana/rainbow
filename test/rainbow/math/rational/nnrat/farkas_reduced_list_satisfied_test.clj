(ns rainbow.math.rational.nnrat.farkas-reduced-list-satisfied-test
  "Farkas elimination reduction correctness (sufficiency): the reduced conditions
  imply the source both-sides system is satisfied.

  Guards:
  1. HOLDS: nnrat/farkas-reduced-list-satisfied is :checked, axiom-free.
  2. ABOUT THE SOURCE (non-vacuous by construction): the conclusion references
     nnrat/farkas-both-sides-rows-satisfied and the premise references
     nnrat/farkas-reduced-conditions -- the statement is source satisfaction from
     reduced conditions, not an existential over fabricated partition lists.
     There is nothing for a tautology-fill to attach to.
  3. CONSUMES THE REVERSE LEMMAS: the proof VALUE mentions
     farkas-lower-to-both-sides and farkas-upper-to-both-sides -- it reconstructs
     each source row from its reduced disjunct and cannot silently drop the
     reconstruction (which is where the premise is actually used).

  Scope: this is REDUCTION CORRECTNESS, not partition provenance (see the module
  docstring and the design notes section 5c).
  Tests only; additive; no direction picked."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-reduced-list-satisfied :as rls]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (rls/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- mentions-const? [term id]
  (cond (not (vector? term)) false
        (and (= :const (first term)) (= (second term) id)) true
        :else (boolean (some #(mentions-const? % id) (rest term)))))

(deftest reduced-list-satisfied-holds
  (testing "farkas-reduced-list-satisfied is proved, axiom-free"
    (let [env @checked-environment
          ids (merge (rls/definition-ids env) (rls/theorem-ids env))]
      (is (= #{'nnrat/farkas-reduced-list-satisfied} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest reduced-list-satisfied-is-about-the-source
  (testing "the statement transports reduced conditions to SOURCE satisfaction --
            no existential partition to fake"
    (let [env @checked-environment
          t (:rainbow/type (environment/declaration
                            env (environment/resolve-id env 'nnrat/farkas-reduced-list-satisfied)))
          sat-id (environment/resolve-id env 'nnrat/farkas-both-sides-rows-satisfied)
          red-id (environment/resolve-id env 'nnrat/farkas-reduced-conditions)]
      (is (mentions-const? t sat-id)
          "conclusion no longer mentions farkas-both-sides-rows-satisfied -- not source satisfaction")
      (is (mentions-const? t red-id)
          "premise no longer mentions farkas-reduced-conditions"))))

(deftest reduced-list-satisfied-consumes-reverse-lemmas
  (testing "the proof reconstructs each source row via reverse lemmas --
            if it dropped them (e.g. a premise-ignoring shortcut) this fails RED"
    (let [env @checked-environment
          v (:rainbow/value (environment/declaration
                             env (environment/resolve-id env 'nnrat/farkas-reduced-list-satisfied)))
          lower-id (environment/resolve-id env 'nnrat/farkas-lower-to-both-sides)
          upper-id (environment/resolve-id env 'nnrat/farkas-upper-to-both-sides)]
      (is (mentions-const? v lower-id)
          "proof no longer uses farkas-lower-to-both-sides")
      (is (mentions-const? v upper-id)
          "proof no longer uses farkas-upper-to-both-sides"))))
