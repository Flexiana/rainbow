(ns rainbow.math.rational.signed.max-three
  "Reusable optimality certificate for a fixed three-candidate maximum.

  Fixed-cardinality selection is the largest honest argmax slice expressible by
  the current scalar Expr/Form language without adding lists, computed indexing,
  or a polymorphic result carrier. `signed/max-three` is an unrolled fold and
  the four theorems prove its exact universal property: every candidate is below
  it, and it is below every common upper bound. Native and axiom-free on D63."
  (:refer-clojure :exclude [max])
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.minmax :as minmax]
            [rainbow.math.rational.signed.order-transitivity :as transitivity]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- decide-at-most [left right]
  (app (function/const* 'signed/decide-at-most []) left right))
(defn- selected-at [at-false at-true choice]
  (app (function/const* 'data/Bool.rec [type-level])
       (function/lam [['ignored bool]] signed)
       at-false at-true choice))
(defn- maximum-three [first-value second-value third-value]
  (app (function/const* 'signed/max-three [])
       first-value second-value third-value))
(defn- transitive [left middle right left-middle middle-right]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right left-middle middle-right))
(defn- eq-signed [left right]
  (function/equality type-level signed left right))
(defn- reflexive-signed [value]
  (app (function/const* 'equality/reflexive [type-level]) signed value))
(defn- disjunction [left right]
  (proposition/disjunction left right))
(defn- choose-left [left right proof]
  (app (function/const* 'proposition/left-disjunct [])
       left right proof))
(defn- choose-right [left right proof]
  (app (function/const* 'proposition/right-disjunct [])
       left right proof))

(def max-three-spec
  {:name 'signed/max-three :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed signed signed)
   :value
   (function/lam
    [['first signed] ['second signed] ['third signed]]
    (maximum (maximum 'first 'second) 'third))})

(def max-three-upper-first-spec
  {:name 'signed/max-three-upper-first :universes []
   :type
   (function/forall
    [['first signed] ['second signed] ['third signed]]
    (at-most 'first (maximum-three 'first 'second 'third)))
   :value
   (function/lam
    [['first signed] ['second signed] ['third signed]]
    (transitive
     'first (maximum 'first 'second)
     (maximum-three 'first 'second 'third)
     (app (function/const* 'signed/max-upper-left []) 'first 'second)
     (app (function/const* 'signed/max-upper-left [])
          (maximum 'first 'second) 'third)))})

(def max-three-upper-second-spec
  {:name 'signed/max-three-upper-second :universes []
   :type
   (function/forall
    [['first signed] ['second signed] ['third signed]]
    (at-most 'second (maximum-three 'first 'second 'third)))
   :value
   (function/lam
    [['first signed] ['second signed] ['third signed]]
    (transitive
     'second (maximum 'first 'second)
     (maximum-three 'first 'second 'third)
     (app (function/const* 'signed/max-upper-right []) 'first 'second)
     (app (function/const* 'signed/max-upper-left [])
          (maximum 'first 'second) 'third)))})

(def max-three-upper-third-spec
  {:name 'signed/max-three-upper-third :universes []
   :type
   (function/forall
    [['first signed] ['second signed] ['third signed]]
    (at-most 'third (maximum-three 'first 'second 'third)))
   :value
   (function/lam
    [['first signed] ['second signed] ['third signed]]
    (app (function/const* 'signed/max-upper-right [])
         (maximum 'first 'second) 'third))})

(def max-three-least-upper-spec
  {:name 'signed/max-three-least-upper :universes []
   :type
   (function/forall
    [['first signed] ['second signed] ['third signed] ['upper signed]
     ['first-upper (at-most 'first 'upper)]
     ['second-upper (at-most 'second 'upper)]
     ['third-upper (at-most 'third 'upper)]]
    (at-most (maximum-three 'first 'second 'third) 'upper))
   :value
   (function/lam
    [['first signed] ['second signed] ['third signed] ['upper signed]
     ['first-upper (at-most 'first 'upper)]
     ['second-upper (at-most 'second 'upper)]
     ['third-upper (at-most 'third 'upper)]]
    (app
     (function/const* 'signed/at-most-max [])
     (maximum 'first 'second) 'third 'upper
     (app (function/const* 'signed/at-most-max [])
          'first 'second 'upper 'first-upper 'second-upper)
     'third-upper))})

(def max-three-is-candidate-spec
  (let [inner-choice (decide-at-most 'first 'second)
        inner-selected (selected-at 'first 'second inner-choice)
        outer-choice (decide-at-most inner-selected 'third)
        choice-proposition
        (fn [result]
          (disjunction
           (eq-signed result 'first)
           (disjunction (eq-signed result 'second)
                        (eq-signed result 'third))))
        outer-motive
        (function/lam
         [['candidate-outer-choice bool]]
         (choice-proposition
          (selected-at inner-selected 'third 'candidate-outer-choice)))
        inner-motive
        (function/lam
         [['candidate-inner-choice bool]]
         (choice-proposition
          (selected-at
           (selected-at 'first 'second 'candidate-inner-choice)
           'third false-value)))
        inner-false
        (choose-left
         (eq-signed 'first 'first)
         (disjunction (eq-signed 'first 'second)
                      (eq-signed 'first 'third))
         (reflexive-signed 'first))
        inner-true
        (choose-right
         (eq-signed 'second 'first)
         (disjunction (eq-signed 'second 'second)
                      (eq-signed 'second 'third))
         (choose-left
          (eq-signed 'second 'second)
          (eq-signed 'second 'third)
          (reflexive-signed 'second)))
        outer-false
        (app (function/const* 'data/Bool.rec [zero-level])
             inner-motive inner-false inner-true inner-choice)
        outer-true
        (choose-right
         (eq-signed 'third 'first)
         (disjunction (eq-signed 'third 'second)
                      (eq-signed 'third 'third))
         (choose-right
          (eq-signed 'third 'second)
          (eq-signed 'third 'third)
          (reflexive-signed 'third)))]
    {:name 'signed/max-three-is-first-or-second-or-third :universes []
     :type
     (function/forall
      [['first signed] ['second signed] ['third signed]]
      (choice-proposition (maximum-three 'first 'second 'third)))
     :value
     (function/lam
      [['first signed] ['second signed] ['third signed]]
      (app (function/const* 'data/Bool.rec [zero-level])
           outer-motive outer-false outer-true outer-choice))}))

(def definition-specs [max-three-spec])
(def theorem-specs
  [max-three-upper-first-spec
   max-three-upper-second-spec
   max-three-upper-third-spec
   max-three-least-upper-spec
   max-three-is-candidate-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      transitivity/extend-environment
      minmax/extend-environment
      (support/extend-with :signed-max-three
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
