(ns rainbow.math.rational.signed.lp-feasibility-bridge
  "Proof-producing assembly of original inequalities/equalities versus actual
  expanded listed constraints. No runtime/verifier changes or executable claim."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-equality-row-bridge :as row]
            [rainbow.math.rational.signed.pointwise-order :as pointwise]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def truth (f/const* 'proposition/truth []))
(defn- both [P Q] (app 'proposition/conjunction P Q))
(defn- conjoin [P Q p q] (app 'proposition/conjoin P Q p q))
(defn- left [P Q h] (app 'proposition/left P Q h))
(defn- right [P Q h] (app 'proposition/right P Q h))
(defn- forward [P Q eq h] (app 'proposition/equivalence-forward P Q eq h))
(defn- backward [P Q eq h] (app 'proposition/equivalence-backward P Q eq h))
(defn- equiv [P Q fwd bwd] (app 'proposition/equivalence-intro P Q fwd bwd))
(defn- mapping [xs]
  (if (seq xs) (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal xs))
      (f/lam [['index lp/nat]] (f/const* 'signed/zero []))))
(defn- dot [coefficients columns]
  (let [m (mapping coefficients)]
    (poly 'signed/map-sum lp/nat
          (f/lam [['i lp/nat]] (app 'signed/multiply (f/app m 'i) (f/app 'candidate 'i))) columns)))
(defn- clause [relation coefficients rhs columns]
  (app relation (dot coefficients columns) (#'lp/signed-literal rhs)))

(defn- assemble [blocks]
  (if (empty? blocks)
    {:original truth :actual truth
     :forward (f/lam [['h truth]] 'h) :backward (f/lam [['h truth]] 'h)}
    (let [{P :original entries :actual eq :equivalence} (first blocks)
          tail (assemble (rest blocks)) O (:original tail) T (:actual tail)
          [A B] entries two? (= 2 (count entries))
          head (if two? (both A B) A)
          rest-type (if two? (both B T) T)
          original (both P O) actual (both A rest-type)
          h (forward P head eq (left P O 'given))
          t (f/app (:forward tail) (right P O 'given))
          actual-head (if two? (conjoin A B (left A rest-type 'given)
                                        (left B T (right A rest-type 'given)))
                          (left A rest-type 'given))
          actual-tail (if two? (right B T (right A rest-type 'given))
                          (right A rest-type 'given))]
      {:original original :actual actual
       :forward (f/lam [['given original]]
                       (if two? (conjoin A rest-type (left A B h) (conjoin B T (right A B h) t))
                           (conjoin A T h t)))
       :backward (f/lam [['given actual]]
                        (conjoin P O (backward P head eq actual-head)
                                 (f/app (:backward tail) actual-tail)))})))

(defn- validate! [original actual]
  (let [eqs (get original :equalities []) n (count (:margins original))
        base (count (:matrix original)) expanded (+ base (* 2 (count eqs)))
        matrices [(:matrix original) (:matrix actual)]
        rhs [(:capacities original) (:capacities actual)]
        shape? (and (map? original) (map? actual) (vector? eqs)
                    (vector? (:margins original)) (vector? (:margins actual))
                    (= n (count (:margins actual))) (<= n 32) (<= expanded 32)
                    (every? vector? matrices) (every? vector? rhs)
                    (= base (count (:capacities original)))
                    (= expanded (count (:matrix actual)) (count (:capacities actual)))
                    (every? #(and (map? %) (vector? (:row %))) eqs)
                    (every? #(and (vector? %) (= n (count %)))
                            (concat (mapcat identity matrices) (map :row eqs))))]
    (when-not shape? (throw (ex-info "Invalid original/expanded constraint dimensions"
                                            {:error/category :lp-feasibility/table-shape})))
    (let [values (concat (mapcat identity (mapcat identity matrices))
                         (mapcat identity rhs) (mapcat :row eqs) (map :value eqs))
          bounded? (fn [x] (and (or (integer? x) (ratio? x))
                                (<= -10000 (if (ratio? x) (numerator x) x) 10000)
                                (<= 1 (if (ratio? x) (denominator x) 1) 10000)))]
      (when-not (every? bounded? values)
        (throw (ex-info "Expected bounded exact constraint data before encoding"
                        {:error/category :lp-feasibility/invalid-scalar}))))))

(defn feasibility-specs
  "Two universal equivalences: all constraints, then constraints plus x>=0.
  Original inequalities precede original equalities in a truth-terminated
  conjunction. Actual target is signed/all-at-most over ALL expanded row indices.
  Exact shape and bounded-exact constraint domain are checked before encoding.
  Nonempty tables use the existing LP lookup; empty lookups default to zero.
  Objective, prices, reported results and supplied plan are outside this scope."
  [original actual]
  (validate! original actual)
  (let [n (count (:margins original)) base (count (:matrix original))
        columns (#'lp/index-list n) row-count (count (:matrix actual))
        inequality-blocks
        (mapv (fn [i]
                (let [o (nth (:matrix original) i) b (nth (:capacities original) i)
                      a (nth (:matrix actual) i) ab (nth (:capacities actual) i)
                      spec (:feasibility-equivalence (row/inequality-row-specs o b a ab))]
                  {:original (clause 'signed/at-most o b columns)
                   :actual [(clause 'signed/at-most a ab columns)]
                   :equivalence (f/app (:value spec) 'candidate)})) (range base))
        equality-blocks
        (mapv (fn [i]
                (let [{o :row b :value} (nth (:equalities original) i)
                      j (+ base (* 2 i)) a (nth (:matrix actual) j) ab (nth (:capacities actual) j)
                      z (nth (:matrix actual) (inc j)) zb (nth (:capacities actual) (inc j))
                      spec (:feasibility-equivalence (row/row-pair-specs o b a ab z zb))]
                  {:original (clause 'signed/equivalent o b columns)
                   :actual [(clause 'signed/at-most a ab columns) (clause 'signed/at-most z zb columns)]
                   :equivalence (f/app (:value spec) 'candidate)})) (range (count (:equalities original))))
        assembled (assemble (into inequality-blocks equality-blocks))
        M (if (pos? row-count)
            (#'lp/nat-lookup (f/arrow lp/nat lp/signed) (mapv mapping (:matrix actual)))
            (f/lam [['row-index lp/nat]] (mapping [])))
        b (mapping (:capacities actual))
        activity (f/lam [['i lp/nat]]
                        (poly 'signed/map-sum lp/nat
                              (f/lam [['j lp/nat]]
                                     (app 'signed/multiply (f/app (f/app M 'i) 'j) (f/app 'candidate 'j))) columns))
        actual-constraints (poly 'signed/all-at-most lp/nat activity b (#'lp/index-list row-count))
        original-constraints (:original assembled)
        ce (equiv original-constraints actual-constraints (:forward assembled) (:backward assembled))
        nonnegative (poly 'signed/all-at-most lp/nat
                          (f/lam [['ignored lp/nat]] (f/const* 'signed/zero [])) 'candidate columns)
        OP (both original-constraints nonnegative) AP (both actual-constraints nonnegative)
        cb [['candidate (f/arrow lp/nat lp/signed)]]]
    {:constraints-equivalence
     {:type (f/forall cb (app 'proposition/equivalence original-constraints actual-constraints))
      :value (f/lam cb ce)}
     :primal-feasibility-equivalence
     {:type (f/forall cb (app 'proposition/equivalence OP AP))
      :value
      (f/lam cb
             (equiv OP AP
                    (f/lam [['holds OP]]
                           (conjoin actual-constraints nonnegative
                                    (forward original-constraints actual-constraints ce
                                             (left original-constraints nonnegative 'holds))
                                    (right original-constraints nonnegative 'holds)))
                    (f/lam [['holds AP]]
                           (conjoin original-constraints nonnegative
                                    (backward original-constraints actual-constraints ce
                                              (left actual-constraints nonnegative 'holds))
                                    (right actual-constraints nonnegative 'holds)))))} }))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-equality-row-bridge rainbow.math.rational.signed.pointwise-order])

(defn install
  "Adds this module's own declarations."
  [env]
  env)

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-feasibility-bridge))
