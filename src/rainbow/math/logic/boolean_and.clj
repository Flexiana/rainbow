(ns rainbow.math.logic.boolean-and
  "General soundness of the boolean AND used across the AHoF membership/monitor rows
  (interval containment, 2-D ODD boxes, polytope halfspaces, ...):

      and a b = if a then b else false      (a Bool.rec over the first operand)

  Proved for ALL booleans a, b:
    and-implies-left  : and a b = true -> a = true
    and-implies-right : and a b = true -> b = true
    and-sound         : and a b = true -> (a = true) AND (b = true)

  The catalog rows established two-clause membership only on worked instances; these
  theorems make the conjunction's soundness universal, so any decidable two-clause test
  (lo<=x AND x<=hi, a1.x<=b1 AND a2.x<=b2, ...) that returns true genuinely entails both
  clauses. Case-split on the first operand via data/Bool.rec; the false branch is
  discharged by bool/false-not-true + proposition/explode. Native and axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))

(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- reflexive-bool [v]
  (function/app (function/const* 'equality/reflexive [type-level]) bool v))
(defn- condition [d] (eq-bool d d))
(defn- and-op [a b] (function/app (function/const* 'boolean/and []) a b))
(defn- conjunction [l r]
  (function/app (function/const* 'proposition/conjunction []) l r))

;; and a b = if-data bool (cond a) a b false  ==  Bool.rec _ false b a
(def and-spec
  {:name 'boolean/and :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam [['a bool] ['b bool]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      bool (condition 'a) 'a 'b false-value))})

(def definition-specs [and-spec])

;; and a b = true -> a = true
(def and-implies-left-spec
  {:name 'boolean/and-implies-left :universes []
   :type (function/forall [['a bool] ['b bool]]
                          (function/arrow (eq-bool (and-op 'a 'b) true-value)
                                          (eq-bool 'a true-value)))
   :value (function/lam
           [['a bool] ['b bool]]
           (function/app
            (function/const* 'data/Bool.rec [zero-level])
            ;; motive av -> ( (and av b = true) -> (av = true) )
            (function/lam [['av bool]]
                          (function/arrow (eq-bool (and-op 'av 'b) true-value)
                                          (eq-bool 'av true-value)))
            ;; a=false: and false b = false ; hyp (false=true) is exactly the goal
            (function/lam [['h (eq-bool (and-op false-value 'b) true-value)]] 'h)
            ;; a=true: goal (true=true)
            (function/lam [['h (eq-bool (and-op true-value 'b) true-value)]]
                          (reflexive-bool true-value))
            'a))})

;; and a b = true -> b = true
(def and-implies-right-spec
  {:name 'boolean/and-implies-right :universes []
   :type (function/forall [['a bool] ['b bool]]
                          (function/arrow (eq-bool (and-op 'a 'b) true-value)
                                          (eq-bool 'b true-value)))
   :value (function/lam
           [['a bool] ['b bool]]
           (function/app
            (function/const* 'data/Bool.rec [zero-level])
            (function/lam [['av bool]]
                          (function/arrow (eq-bool (and-op 'av 'b) true-value)
                                          (eq-bool 'b true-value)))
            ;; a=false: and false b = false ; hyp (false=true) -> explode
            (function/lam [['h (eq-bool (and-op false-value 'b) true-value)]]
                          (function/app
                           (function/const* 'proposition/explode [])
                           (eq-bool 'b true-value)
                           (function/app (function/const* 'bool/false-not-true []) 'h)))
            ;; a=true: and true b = b ; hyp (b=true) is the goal
            (function/lam [['h (eq-bool (and-op true-value 'b) true-value)]] 'h)
            'a))})

;; and a b = true -> (a=true) AND (b=true)
(def and-sound-spec
  {:name 'boolean/and-sound :universes []
   :type (function/forall [['a bool] ['b bool]]
                          (function/arrow (eq-bool (and-op 'a 'b) true-value)
                                          (conjunction (eq-bool 'a true-value)
                                                       (eq-bool 'b true-value))))
   :value (function/lam
           [['a bool] ['b bool] ['h (eq-bool (and-op 'a 'b) true-value)]]
           (function/app
            (function/const* 'proposition/conjoin [])
            (eq-bool 'a true-value) (eq-bool 'b true-value)
            (function/app (function/const* 'boolean/and-implies-left []) 'a 'b 'h)
            (function/app (function/const* 'boolean/and-implies-right []) 'a 'b 'h)))})

(def theorem-specs
  [and-implies-left-spec and-implies-right-spec and-sound-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :boolean-and
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
