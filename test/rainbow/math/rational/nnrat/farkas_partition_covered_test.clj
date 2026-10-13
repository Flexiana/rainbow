(ns rainbow.math.rational.nnrat.farkas-partition-covered-test
  "The vacuity FIX for the partition keystone, and its regression protection.

  nnrat/farkas-partition-list-covered strengthens farkas-partition-list-necessary
  with a covering conjunct length(l)+length(u)=length(rows) that ties the output
  to the input, so the empty witness no longer inhabits it (verified separately
  in nnrat_farkas_partition_covering_design_test).

  A fix that regresses must show up RED, not as a quietly-empty pass. Two guards:
  1. the covered theorem is :checked, axiom-free (a broken proof -> red);
  2. the covered theorem's stated TYPE still carries the covering -- it references
     list/length and algebra/nat-add. If someone reverts it to the vacuous
     EXISTS-sat-only conclusion, those constants vanish from the type and this
     assertion fails RED. This ties the non-vacuity to the SHIPPED theorem's
     type, catching a revert-to-vacuous that a plain :checked test would miss
     (the vacuous form is also :checked).

  Tests only; no proved brick edited (the covered theorem is a NEW, additive
  theorem; the original farkas-partition-list-necessary is untouched)."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-partition-covered :as covered]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (covered/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- mentions-const? [term id]
  (cond (not (vector? term)) false
        (and (= :const (first term)) (= (second term) id)) true
        :else (boolean (some #(mentions-const? % id) (rest term)))))

(deftest covered-theorem-holds
  (testing "the covering-strengthened partition theorem is proved, axiom-free"
    (let [env @checked-environment
          ids (merge (covered/definition-ids env) (covered/theorem-ids env))]
      (is (= #{'nnrat/farkas-partition-list-covered} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest covered-type-still-carries-the-covering
  (testing "the covered theorem's TYPE references list/length and algebra/nat-add
            -- i.e. the covering conjunct is present. If someone reverts it to the
            vacuous EXISTS-sat-only conclusion, these constants drop out and this
            fails RED (a plain :checked test would not, since the vacuous form is
            also :checked)."
    (let [env @checked-environment
          t (:rainbow/type (environment/declaration
                            env (environment/resolve-id env 'nnrat/farkas-partition-list-covered)))
          length-id (environment/resolve-id env 'list/length)
          nat-add-id (environment/resolve-id env 'algebra/nat-add)]
      (is (some? length-id) "list/length not resolvable")
      (is (some? nat-add-id) "algebra/nat-add not resolvable")
      (is (mentions-const? t length-id)
          "farkas-partition-list-covered's TYPE no longer mentions list/length --
           the covering conjunct was stripped; the theorem regressed to vacuous.")
      (is (mentions-const? t nat-add-id)
          "farkas-partition-list-covered's TYPE no longer mentions algebra/nat-add
           -- the covering length equation was removed; the theorem regressed."))))
