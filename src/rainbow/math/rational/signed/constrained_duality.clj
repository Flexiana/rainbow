(ns rainbow.math.rational.signed.constrained-duality
  "Lagrangian duality with a CONCRETE penalty: an explicit finite constraint
  system with explicit multipliers.

  `rainbow.math.rational.signed.lagrangian-duality` proves weak duality, zero-gap
  optimality and complementary slackness from an abstract `penalty` function
  together with the hypothesis that the penalty is nonpositive on the feasible
  set.  That hypothesis is the only thing standing between those theorems and an
  ordinary constrained program.  Here it is discharged.

  Given an index type A, multipliers `lambda : A -> signed`, constraint functions
  `g : A -> signed -> signed` and an index list, the penalty is the finite sum

      penalty x  =  sum_i  lambda_i * g_i x

  and `optimization/signed-constraint-penalty-nonpositive` derives its
  nonpositivity from the two ordinary side conditions of a Lagrangian relaxation:

      0 <= lambda_i          (dual feasibility, nonnegative multipliers)
      g_i x <= 0             (primal feasibility, satisfied constraints)

  termwise by the multiplicative sign rule, then through the sum by
  `signed/map-sum-nonpositive`.  Composing gives

      optimization/signed-constrained-weak-duality
      optimization/signed-constrained-zero-gap-optimal

  -- weak duality and the primal optimality certificate for a genuine finite
  constraint system, with no abstract penalty left in the statement.

  Native and axiom-free; chains the signed finite-sum, multiplicative sign-rule
  and Lagrangian duality modules on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.lagrangian-duality :as duality]
            [rainbow.math.rational.signed.list-sum :as sum]
            [rainbow.math.rational.signed.multiply-order :as sign]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def objective (function/arrow signed signed))
(def predicate (function/arrow signed 'Prop))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- map-sum [A f xs] (app (function/const* 'signed/map-sum [U]) A f xs))

(def constraint-family
  (function/arrow 'A (function/arrow signed signed)))
(def multiplier-family (function/arrow 'A signed))

;; the summand at index i, evaluated at x
(defn- term [lambda g x]
  (function/lam [['i 'A]]
                (smul (app lambda 'i) (app (app g 'i) x))))

(defn- penalty-at [A lambda g idx x]
  (map-sum A (term lambda g x) idx))

(defn- penalty-function [A lambda g idx]
  (function/lam [['y signed]] (penalty-at A lambda g idx 'y)))

(defn- multipliers-nonnegative [lambda]
  (function/forall [['i 'A]] (sle signed-zero (app lambda 'i))))

(defn- constraints-satisfied [g x]
  (function/forall [['i 'A]] (sle (app (app g 'i) x) signed-zero)))

;; ---- the penalty of a satisfied constraint system is nonpositive ------------

(def penalty-nonpositive-spec
  {:name 'optimization/signed-constraint-penalty-nonpositive :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['lambda multiplier-family]
     ['g constraint-family]
     ['idx (list-of 'A)]
     ['nonnegative (multipliers-nonnegative 'lambda)]
     ['x signed]
     ['satisfied (constraints-satisfied 'g 'x)]]
    (sle (penalty-at 'A 'lambda 'g 'idx 'x) signed-zero))
   :value
   (function/lam
    [['A type-u]
     ['lambda multiplier-family]
     ['g constraint-family]
     ['idx (list-of 'A)]
     ['nonnegative (multipliers-nonnegative 'lambda)]
     ['x signed]
     ['satisfied (constraints-satisfied 'g 'x)]]
    (app (function/const* 'signed/map-sum-nonpositive [U])
         'A
         (term 'lambda 'g 'x)
         (function/lam
          [['i 'A]]
          (app (function/const*
                'optimization/signed-multiplier-penalty-nonpositive [])
               (app 'lambda 'i) (app (app 'g 'i) 'x)
               (app 'nonnegative 'i) (app 'satisfied 'i)))
         'idx))})

;; ---- concrete weak duality --------------------------------------------------

(defn- bound-type [f A lambda g idx dual]
  (function/forall
   [['y signed]]
   (sle dual (sadd (app f 'y) (penalty-at A lambda g idx 'y)))))

(defn- feasibility-type [g feasible]
  (function/forall
   [['y signed] ['member (app feasible 'y)]]
   (constraints-satisfied g 'y)))

(def constrained-weak-duality-spec
  {:name 'optimization/signed-constrained-weak-duality :universes ['u]
   :type
   (function/forall
    [['A type-u] ['f objective]
     ['lambda multiplier-family] ['g constraint-family]
     ['idx (list-of 'A)] ['feasible predicate] ['dual signed]
     ['bound (bound-type 'f 'A 'lambda 'g 'idx 'dual)]
     ['nonnegative (multipliers-nonnegative 'lambda)]
     ['satisfied (feasibility-type 'g 'feasible)]
     ['x signed] ['member (app 'feasible 'x)]]
    (sle 'dual (app 'f 'x)))
   :value
   (function/lam
    [['A type-u] ['f objective]
     ['lambda multiplier-family] ['g constraint-family]
     ['idx (list-of 'A)] ['feasible predicate] ['dual signed]
     ['bound (bound-type 'f 'A 'lambda 'g 'idx 'dual)]
     ['nonnegative (multipliers-nonnegative 'lambda)]
     ['satisfied (feasibility-type 'g 'feasible)]
     ['x signed] ['member (app 'feasible 'x)]]
    (app (function/const* 'optimization/signed-lagrangian-weak-duality [])
         'f (penalty-function 'A 'lambda 'g 'idx) 'feasible 'dual
         'bound
         (function/lam
          [['y signed] ['member-y (app 'feasible 'y)]]
          (app (function/const*
                'optimization/signed-constraint-penalty-nonpositive [U])
               'A 'lambda 'g 'idx 'nonnegative 'y
               (app 'satisfied 'y 'member-y)))
         'x 'member))})

(def constrained-zero-gap-spec
  {:name 'optimization/signed-constrained-zero-gap-optimal :universes ['u]
   :type
   (function/forall
    [['A type-u] ['f objective]
     ['lambda multiplier-family] ['g constraint-family]
     ['idx (list-of 'A)] ['feasible predicate] ['dual signed]
     ['bound (bound-type 'f 'A 'lambda 'g 'idx 'dual)]
     ['nonnegative (multipliers-nonnegative 'lambda)]
     ['satisfied (feasibility-type 'g 'feasible)]
     ['x0 signed] ['x0-member (app 'feasible 'x0)]
     ['gap (seq-equiv 'dual (app 'f 'x0))]
     ['x signed] ['member (app 'feasible 'x)]]
    (sle (app 'f 'x0) (app 'f 'x)))
   :value
   (function/lam
    [['A type-u] ['f objective]
     ['lambda multiplier-family] ['g constraint-family]
     ['idx (list-of 'A)] ['feasible predicate] ['dual signed]
     ['bound (bound-type 'f 'A 'lambda 'g 'idx 'dual)]
     ['nonnegative (multipliers-nonnegative 'lambda)]
     ['satisfied (feasibility-type 'g 'feasible)]
     ['x0 signed] ['x0-member (app 'feasible 'x0)]
     ['gap (seq-equiv 'dual (app 'f 'x0))]
     ['x signed] ['member (app 'feasible 'x)]]
    (app (function/const*
          'optimization/signed-lagrangian-zero-gap-primal-optimal [])
         'f (penalty-function 'A 'lambda 'g 'idx) 'feasible 'dual
         'bound
         (function/lam
          [['y signed] ['member-y (app 'feasible 'y)]]
          (app (function/const*
                'optimization/signed-constraint-penalty-nonpositive [U])
               'A 'lambda 'g 'idx 'nonnegative 'y
               (app 'satisfied 'y 'member-y)))
         'x0 'x0-member 'gap 'x 'member))})

(def definition-specs [])
(def theorem-specs
  [penalty-nonpositive-spec
   constrained-weak-duality-spec
   constrained-zero-gap-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      sum/extend-environment
      sign/extend-environment
      duality/extend-environment
      (support/extend-with :signed-constrained-duality theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
