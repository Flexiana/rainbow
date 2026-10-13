(ns rainbow.nnrat-farkas-source-countermodel-test
  "A formal countermodel to premise-free satisfaction of all source LP rows.
  The singleton (0,0,1,0) is unsatisfied at EVERY evaluation point, whereas
  dropping it gives a satisfied empty list. Negative statements are proved,
  kernel-rechecked and axiom-audited, not inferred from a failed proof attempt."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.logic.proposition :as p]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.farkas-reduce-list :as reduction]
            [rainbow.math.rational.nnrat.order-nontrivial :as nontrivial]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(def ^:private tl [:succ [:zero]])
(def ^:private R reduction/nnrat)
(def ^:private zero (f/const* 'nnrat/zero []))
(def ^:private one (f/const* 'nnrat/one []))
(defn- pair [a b x y] (f/app (f/const* 'data/pair [tl tl]) a b x y))
(def ^:private impossible-row
  (pair R reduction/bpq zero (pair R reduction/pq zero (pair R R one zero))))
(def ^:private empty-rows (f/app (f/const* 'data/nil [tl]) reduction/row))
(def ^:private impossible-rows
  (f/app (f/const* 'data/cons [tl]) reduction/row impossible-row empty-rows))
(defn- satisfied [rows w] (app 'nnrat/farkas-both-sides-rows-satisfied rows w))
(defn- impossible-row-condition [w]
  (app 'nnrat/at-most
       (app 'nnrat/add (app 'nnrat/multiply zero w) one)
       (app 'nnrat/add (app 'nnrat/multiply zero w) zero)))

(def ^:private singleton-unsatisfied-spec
  {:name 'audit/farkas-unit-source-row-never-satisfied
   :universes []
   :type (f/forall [['w R]] (p/negation (satisfied impossible-rows 'w)))
   :value
   (f/lam [['w R] ['holds (satisfied impossible-rows 'w)]]
          (app 'nnrat/common-add-unit-gap-impossible (app 'nnrat/multiply zero 'w)
               (app 'proposition/left (impossible-row-condition 'w)
                    (satisfied empty-rows 'w) 'holds)))})

(def ^:private universal-source-satisfaction
  (f/forall [['rows reduction/list-row] ['w R]] (satisfied 'rows 'w)))
(def ^:private no-universal-source-satisfaction-spec
  {:name 'audit/farkas-not-all-source-systems-satisfied
   :universes []
   :type (p/negation universal-source-satisfaction)
   :value
   (f/lam [['all universal-source-satisfaction]]
          (app 'audit/farkas-unit-source-row-never-satisfied zero
               (f/app 'all impossible-rows zero)))})

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (-> (:environment checkpoint)
          reduction/extend-environment
          nontrivial/extend-environment
          (support/extend-with ::countermodel
                               [singleton-unsatisfied-spec no-universal-source-satisfaction-spec])))))

(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "Countermodel expression did not elaborate" {:result r})))
    (:term r)))

(deftest source-countermodel-and-order-lemmas-are-proved-without-axioms
  (let [env @checked-environment]
    (doseq [spec (concat nontrivial/theorem-specs
                        [singleton-unsatisfied-spec no-universal-source-satisfaction-spec])]
      (let [id (environment/resolve-id env (:name spec))
            d (environment/declaration env id)]
        (is (some? id) (str (:name spec)))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{}))))
        (is (= #{} (kernel/axioms env id)))))))

(deftest dropping-the-infeasible-source-row-is-observably-weaker
  (let [env @checked-environment
        ;; Truth proves satisfaction of an empty system at arbitrary w.
        candidate (f/lam [['w R]] (f/const* 'proposition/trivial []))
        value (elaborate! env candidate)
        empty-type (elaborate! env (f/forall [['w R]] (satisfied empty-rows 'w)))
        singleton-type (elaborate! env (f/forall [['w R]] (satisfied impossible-rows 'w)))]
    (is (= :checked (:status (kernel/check env value empty-type #{}))))
    (is (= :rejected (:status (kernel/check env value singleton-type #{}))))))
