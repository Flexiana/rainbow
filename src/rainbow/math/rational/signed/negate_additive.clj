(ns rainbow.math.rational.signed.negate-additive
  "Signed negation distributes over addition up to signed equivalence.

    -(a + b)  ~  (-a) + (-b)

  Both sides reduce to the same Grothendieck pair: negation swaps the positive
  and negative sums, while adding the two negated inputs builds those same sums.
  Signed equivalence reflexivity therefore supplies the proof."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))

(def negate-additive-spec
  {:name 'signed/negate-additive :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (equivalent
     (negate (add 'left 'right))
     (add (negate 'left) (negate 'right))))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (app (function/const* 'signed/equivalent-reflexive [])
         (negate (add 'left 'right))))})

(def definition-specs [])
(def theorem-specs [negate-additive-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :signed-negate-additive
                       theorem-specs))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
