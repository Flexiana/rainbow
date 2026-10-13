(ns rainbow.math.linear.matrix.associativity-counterexample
  "A checked counterexample to unrestricted native matrix associativity.

  With A = [[]], B = [], and C = [[0]], both adjacent pairs are composable,
  yet (A*B)*C evaluates to [[0]] while A*(B*C) evaluates to [[]].  Thus the
  nonempty-middle premise of matrix/multiply-associative-nonempty-middle is
  mathematically necessary for the total row-list encoding, not merely a proof
  artifact.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.composable-transpose :as transpose-composable]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def falsity (function/const* 'proposition/falsity []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- composable [left right]
  (app (function/const* 'matrix/composable []) left right))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- counter-left []
  (function/const* 'matrix/associativity-counterexample-left []))
(defn- counter-middle []
  (function/const* 'matrix/associativity-counterexample-middle []))
(defn- counter-right []
  (function/const* 'matrix/associativity-counterexample-right []))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- negation [claim]
  (function/arrow claim falsity))

(def counter-left-spec
  {:name 'matrix/associativity-counterexample-left
   :kind :definition :universes []
   :type matrix-type
   :value (cons-matrix (nil-vector) (nil-matrix))})

(def counter-middle-spec
  {:name 'matrix/associativity-counterexample-middle
   :kind :definition :universes []
   :type matrix-type
   :value (nil-matrix)})

(def counter-right-spec
  {:name 'matrix/associativity-counterexample-right
   :kind :definition :universes []
   :type matrix-type
   :value
   (cons-matrix
    (cons-vector signed-zero (nil-vector))
    (nil-matrix))})

(def counter-left-middle-composable-spec
  {:name 'matrix/associativity-counterexample-left-middle-composable
   :universes []
   :type (composable (counter-left) (counter-middle))
   :value
   (let [inner
         (compatible (counter-left) (column-shape (counter-middle)))
         right-rectangular (rectangular (counter-middle))]
     (conjoin
      inner right-rectangular
      (conjoin
       (same-shape (nil-vector) (nil-vector))
       (compatible (nil-matrix) (nil-vector))
       trivial trivial)
      trivial))})

(def counter-middle-right-composable-spec
  {:name 'matrix/associativity-counterexample-middle-right-composable
   :universes []
   :type (composable (counter-middle) (counter-right))
   :value
   (conjoin
    (compatible (counter-middle) (column-shape (counter-right)))
    (rectangular (counter-right))
    trivial trivial)})

(def counter-left-evaluates-spec
  {:name 'matrix/associativity-counterexample-left-evaluates
   :universes []
   :type
   (matrix-equivalent
    (multiply
     (multiply (counter-left) (counter-middle))
     (counter-right))
    (cons-matrix
     (cons-vector signed-zero (nil-vector))
     (nil-matrix)))
   :value
   (app (function/const* 'matrix/equivalent-reflexive [])
        (cons-matrix
         (cons-vector signed-zero (nil-vector))
         (nil-matrix)))})

(def counter-right-evaluates-spec
  {:name 'matrix/associativity-counterexample-right-evaluates
   :universes []
   :type
   (matrix-equivalent
    (multiply
     (counter-left)
     (multiply (counter-middle) (counter-right)))
    (cons-matrix (nil-vector) (nil-matrix)))
   :value
   (app (function/const* 'matrix/equivalent-reflexive [])
        (cons-matrix (nil-vector) (nil-matrix)))})

(def counter-not-associative-spec
  (let [left-bracketing
        (multiply
         (multiply (counter-left) (counter-middle))
         (counter-right))
        right-bracketing
        (multiply
         (counter-left)
         (multiply (counter-middle) (counter-right)))
        claim (matrix-equivalent left-bracketing right-bracketing)
        impossible-head
        (vector-equivalent
         (cons-vector signed-zero (nil-vector))
         (nil-vector))
        tails-same
        (matrix-equivalent (nil-matrix) (nil-matrix))]
    {:name 'matrix/associativity-counterexample-not-associative
     :universes []
     :type (negation claim)
     :value
     (function/lam
      [['claimed claim]]
      (proposition-left impossible-head tails-same 'claimed))}))

(def definition-specs
  [counter-left-spec counter-middle-spec counter-right-spec])
(def theorem-specs
  [counter-left-middle-composable-spec
   counter-middle-right-composable-spec
   counter-left-evaluates-spec
   counter-right-evaluates-spec
   counter-not-associative-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.composable-transpose])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-associativity-counterexample (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.associativity-counterexample))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
