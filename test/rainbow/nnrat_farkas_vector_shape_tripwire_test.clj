(ns rainbow.nnrat-farkas-vector-shape-tripwire-test
  "FUTURE-PROOFING tripwire for the LP coefficient-vector lane: catch a NEW
  theorem going empty-vacuous, not just the ones already documented.

  The vacuity of the five has a
  syntactic signature: a conclusion of the form `EXISTS carrier, ...` where the
  carrier CONTAINS a data/List (an emptyable list, or a product of them). A
  fold over the empty list is truth, so the empty witness inhabits it. The
  hardcoded vacuity tests only cover the five KNOWN cases; a theorem added
  later with this same shape would slip past them.

  This test auto-enumerates the lane's theorems and asserts that the set whose
  conclusion has the EXISTS-List shape is EXACTLY the three known
  EXISTS-List-vacuous theorems (round, step, partition-list-necessary). It is
  self-validating in both directions:
    - if a NEW theorem acquires the EXISTS-List shape, it appears in the flagged
      set and is not in the known set -> FAILURE (audit it: is it vacuous? if a
      genuine, input-tied existential, refine the classifier; if vacuous,
      document + add a witness test);
    - if the classifier stops detecting the shape (e.g. a refactor changes how
      existence is applied), the three known ones drop out of the flagged set
      -> FAILURE (the detector rotted).

  Scope: covers the lane modules listed below; a theorem in a NEW module is not
  covered until its theorem-ids accessor is added here. Detects the DIRECT
  proposition/existence-over-List shape only; the identity-vacuity kind
  (feasible-step / eliminate, conclusion `feasible zero`) is covered by the
  hardcoded vacuity tests instead. Tests only; no proved brick edited."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.set :as set]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.math.rational.nnrat.farkas-vector-step :as vector-step]
            [rainbow.math.rational.nnrat.farkas-vector-round :as vector-round]
            [rainbow.math.rational.nnrat.farkas-vector-unit-column :as unit-column]
            [rainbow.math.rational.nnrat.farkas-vector-adapter-bilist :as adapter-bilist]
            [rainbow.math.rational.nnrat.farkas-vector-adapter-list :as adapter-list]
            [rainbow.math.rational.nnrat.farkas-vector-partition-fold :as partition-fold]
            [rainbow.math.rational.nnrat.farkas-vector-partition-pack :as partition-pack]
            [rainbow.math.rational.nnrat.farkas-vector-both-sides :as vector-both-sides]
            [rainbow.math.rational.nnrat.farkas-vector-both-sides-reduce :as both-sides-reduce]
            [rainbow.math.rational.nnrat.farkas-cross-vectors :as cross-vectors]
            [rainbow.math.rational.nnrat.farkas-cross-vectors-list :as cross-vectors-list]
            [rainbow.math.rational.nnrat.farkas-cross-vectors-bilist :as cross-vectors-bilist]
            [rainbow.math.rational.nnrat.farkas-partition-list :as partition-list]
            [rainbow.math.rational.nnrat.farkas-eliminate-base :as eliminate-base]
            [rainbow.math.rational.nnrat.farkas-eliminate-all :as eliminate-all]))

;; the three theorems whose conclusion is legitimately (and vacuously) EXISTS
;; over a List carrier -- documented in the design notes
(def ^:private known-exists-list-vacuous
  #{'nnrat/farkas-vector-round
    'nnrat/farkas-vector-step
    'nnrat/farkas-partition-list-necessary})

(def ^:private lane-theorem-id-fns
  [vector-step/theorem-ids vector-round/theorem-ids unit-column/theorem-ids
   adapter-bilist/theorem-ids adapter-list/theorem-ids partition-fold/theorem-ids
   partition-pack/theorem-ids vector-both-sides/theorem-ids
   both-sides-reduce/theorem-ids cross-vectors/theorem-ids
   cross-vectors-list/theorem-ids cross-vectors-bilist/theorem-ids
   partition-list/theorem-ids eliminate-base/theorem-ids eliminate-all/theorem-ids])

(def ^:private lane-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      ;; vector-step transitively installs round, unit-column, the adapters,
      ;; the folds, cross-vectors*, partition-list, eliminate-all and
      ;; both-sides-reduce; add only what its require-chain does not cover.
      (-> (:environment checkpoint)
          vector-step/extend-environment
          partition-pack/extend-environment
          vector-both-sides/extend-environment
          eliminate-base/extend-environment))))

(defn- strip-pi [t]
  (loop [t t] (if (and (vector? t) (= :pi (first t))) (recur (nth t 2)) t)))

(defn- app-head [t]
  (loop [t t] (if (and (vector? t) (= :app (first t))) (recur (nth t 1)) t)))

(defn- app-args [t]
  (loop [t t acc ()] (if (and (vector? t) (= :app (first t))) (recur (nth t 1) (conj acc (nth t 2))) acc)))

(defn- contains-const? [t id]
  (cond (not (vector? t)) false
        (and (= :const (first t)) (= (second t) id)) true
        :else (boolean (some #(contains-const? % id) (rest t)))))

(defn- exists-list-shaped? [env exist-id list-id t]
  (let [concl (strip-pi t)]
    (when (and (vector? concl) (= :app (first concl)))
      (let [h (app-head concl)]
        (when (and (vector? h) (= :const (first h)) (= (second h) exist-id))
          (contains-const? (first (app-args concl)) list-id))))))

(deftest exists-list-shape-is-exactly-the-known-vacuous-set
  (testing "no NEW lane theorem has acquired the EXISTS-over-a-List conclusion
            shape (the empty-vacuity signature) beyond the three documented
            ones; and the classifier still detects those three."
    (let [env @lane-environment
          exist-id (environment/resolve-id env 'proposition/existence)
          list-id (environment/resolve-id env 'data/List)
          names (sort (distinct (mapcat (fn [f] (keys (f env))) lane-theorem-id-fns)))
          flagged (set (filter (fn [nm]
                                 (let [t (:rainbow/type (environment/declaration
                                                         env (environment/resolve-id env nm)))]
                                   (exists-list-shaped? env exist-id list-id t)))
                               names))]
      (is (some? exist-id) "proposition/existence not resolvable")
      (is (some? list-id) "data/List not resolvable")
      (is (pos? (count names)) "no lane theorems enumerated -- module wiring changed")
      ;; detector still works: every known-vacuous EXISTS-List theorem is flagged
      (is (every? flagged known-exists-list-vacuous)
          (str "the EXISTS-List classifier no longer flags a known-vacuous "
               "theorem -- the detector rotted. flagged=" flagged))
      ;; no NEW EXISTS-List theorem: flagged set is exactly the known set
      (is (= flagged known-exists-list-vacuous)
          (str "a lane theorem has the EXISTS-over-a-List conclusion shape "
               "(empty-vacuity signature) but is NOT in the documented set: "
               (vec (sort (set/difference flagged known-exists-list-vacuous)))
               ". Audit it against the design notes -- if "
               "vacuous, document it and add a witness test; if it is a genuine "
               "input-tied existential, refine the classifier and this set.")))))
