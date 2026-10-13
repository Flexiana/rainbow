(ns rainbow.math.rational.signed.square-minimizer-unique
  "Concrete OR-Commons decision object: the square objective (\\x. x*x) has at most one minimizer
  (up to equivalence). A direct instance of signed/strict-convex-minimizer-unique at the proved
  signed/square-strict-convex witness -- demonstrates the general uniqueness theorem on a named
  objective. Light: square-strict-convex is cited opaquely, so no square-instance reduction."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.strict-convex-unique :as unique]
            [rainbow.math.rational.signed.square-strict-convex :as square]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private nnzero (function/const* 'nnrat/zero []))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- nn-lt [a b] (app (function/const* 'nnrat/less-than []) a b))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))
(def ^:private falsity (function/const* 'proposition/falsity []))
(def ^:private square-fn (function/lam [['x signed]] (smul 'x 'x)))
(defn- is-min [f x] (app (function/const* 'signed/is-minimizer []) f x))
(defn- unique-of [f x y w0 w1 hf hx hy hw0 hw1 hw hxy]
  (app (function/const* 'signed/strict-convex-minimizer-unique []) f x y w0 w1 hf hx hy hw0 hw1 hw hxy))
(def ^:private square-strict-convex (function/const* 'signed/square-strict-convex []))

(def square-minimizer-unique-spec
  {:name 'signed/square-minimizer-unique
   :universes []
   :type (function/forall
          [['x signed] ['y signed] ['w0 nnrat] ['w1 nnrat]
           ['hx (is-min square-fn 'x)] ['hy (is-min square-fn 'y)]
           ['hw0 (nn-lt nnzero 'w0)] ['hw1 (nn-lt nnzero 'w1)]
           ['hw (nn-equiv (radd 'w0 'w1) rone)] ['hxy (pneg (seqv 'x 'y))]]
          falsity)
   :value
   (function/lam
    [['x signed] ['y signed] ['w0 nnrat] ['w1 nnrat]
     ['hx (is-min square-fn 'x)] ['hy (is-min square-fn 'y)]
     ['hw0 (nn-lt nnzero 'w0)] ['hw1 (nn-lt nnzero 'w1)]
     ['hw (nn-equiv (radd 'w0 'w1) rone)] ['hxy (pneg (seqv 'x 'y))]]
    (unique-of square-fn 'x 'y 'w0 'w1 square-strict-convex
               'hx 'hy 'hw0 'hw1 'hw 'hxy))})

(def theorem-specs [square-minimizer-unique-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      unique/extend-environment
      square/extend-environment
      (support/extend-with :signed-square-minimizer-unique theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
