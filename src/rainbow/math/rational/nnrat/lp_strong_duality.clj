(ns rainbow.math.rational.nnrat.lp-strong-duality
  "Concrete textbook strong duality for a verified Bool-indexed 2x2 LP.

  Instance (rows and columns enumerate [true,false]):
      maximize  x_0 + x_1
      subject to x_0 + x_1 <= 2 in each row, x >= 0.

  The exhibited primal point is x=(1,1), and the exhibited dual point is
  y=(1,0).  The named theorem bundles all five facts that make this a genuine
  strong-duality witness: x is primal feasible, y is dual feasible, their
  objectives are equivalent, x bounds every primal-feasible alternative from
  above, and y bounds every dual-feasible alternative from below.

    nnrat/lp-example-strong-duality :
      primal-feasible(x)
      /\\ dual-feasible(y)
      /\\ c.x ~ b.y
      /\\ (forall x', primal-feasible(x') -> c.x' <= c.x)
      /\\ (forall y', dual-feasible(y') -> b.y <= b.y')

  The two optimality components instantiate the general primal and dual LP
  optimality certificates.  All evidence is native proof data and axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.lp-optimality :as opt]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def tt (function/const* 'data/true []))
(def ff (function/const* 'data/false []))
(def one (function/const* 'nnrat/one []))
(def rzero (function/const* 'nnrat/zero []))

(defn- make [n decimal-places]
  (function/app
   (function/const* 'nnrat/make [])
   (nth (iterate #(function/app (function/const* 'data/succ []) %)
                 (function/const* 'data/zero []))
        n)
   (nth (iterate #(function/app (function/const* 'data/succ []) %)
                 (function/const* 'data/zero []))
        decimal-places)))

(def two (make 2 0))

(defn- app [f x] (function/app f x))
(defn- lam [variable type body] (function/lam [[variable type]] body))
(defn- arrow [left right] (function/arrow left right))
(defn- rmul [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- rat-le [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- equiv [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- at-most-refl [value]
  (function/app (function/const* 'nnrat/at-most-reflexive []) value))
(defn- equiv-refl [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- cons-bool [head tail]
  (function/app (function/const* 'data/cons [type-level]) bool head tail))
(def nil-bool
  (function/app (function/const* 'data/nil [type-level]) bool))
(defn- map-sum [f values]
  (function/app (function/const* 'nnrat/map-sum [zero-level])
                bool f values))
(defn- bool-rec-prop [motive false-case true-case value]
  (function/app (function/const* 'data/Bool.rec [[:zero]])
                motive false-case true-case value))
(defn- bool-rec-nnrat [motive false-case true-case value]
  (function/app (function/const* 'data/Bool.rec [type-level])
                motive false-case true-case value))

;; A is all ones; b is constantly two; c and x are constantly one.
(def A (lam 'i bool (lam 'j bool one)))
(def bvec (lam 'i bool two))
(def cvec (lam 'j bool one))
(def xvec (lam 'j bool one))
(def yvec
  (lam 'i bool
       (bool-rec-nnrat (lam 'ignored bool nnrat) rzero one 'i)))
(def rows (cons-bool tt (cons-bool ff nil-bool)))
(def cols rows)

(defn- Ax-row [x i]
  (map-sum (lam 'j bool (rmul (app (app A i) 'j) (app x 'j))) cols))
(defn- ATy-col [y j]
  (map-sum (lam 'i bool (rmul (app (app A 'i) j) (app y 'i))) rows))
(defn- cdotx [x]
  (map-sum (lam 'j bool (rmul (app cvec 'j) (app x 'j))) cols))
(defn- bdoty [y]
  (map-sum (lam 'i bool (rmul (app bvec 'i) (app y 'i))) rows))
(defn- primal-feasible [x]
  (function/forall [['i bool]] (rat-le (Ax-row x 'i) (app bvec 'i))))
(defn- dual-feasible [y]
  (function/forall [['j bool]] (rat-le (app cvec 'j) (ATy-col y 'j))))

(def hp
  (lam 'i bool
       (bool-rec-prop
        (lam 'iv bool (rat-le (Ax-row xvec 'iv) (app bvec 'iv)))
        (at-most-refl two)
        (at-most-refl two)
        'i)))

(def hd
  (lam 'j bool
       (bool-rec-prop
        (lam 'jv bool (rat-le (app cvec 'jv) (ATy-col yvec 'jv)))
        (at-most-refl one)
        (at-most-refl one)
        'j)))

(def hgap (equiv-refl two))

(def primal-optimal
  (function/forall
   [['x-alt (arrow bool nnrat)]
    ['hp-alt (primal-feasible 'x-alt)]]
   (rat-le (cdotx 'x-alt) (cdotx xvec))))

(def dual-optimal
  (function/forall
   [['y-alt (arrow bool nnrat)]
    ['hd-alt (dual-feasible 'y-alt)]]
   (rat-le (bdoty yvec) (bdoty 'y-alt))))

(def strong-duality-claim
  (proposition/conjunction
   (primal-feasible xvec)
   (proposition/conjunction
    (dual-feasible yvec)
    (proposition/conjunction
     (equiv (cdotx xvec) (bdoty yvec))
     (proposition/conjunction primal-optimal dual-optimal)))))

(def strong-duality-spec
  {:name 'nnrat/lp-example-strong-duality
   :universes []
   :type strong-duality-claim
   :value
   (let [primal-optimal-proof
         (function/lam
          [['x-alt (arrow bool nnrat)]
           ['hp-alt (primal-feasible 'x-alt)]]
          (function/app
           (function/const* 'nnrat/lp-optimality-certificate [zero-level])
           bool bool A bvec cvec xvec yvec rows cols hp hd hgap
           'x-alt 'hp-alt))
         dual-optimal-proof
         (function/lam
          [['y-alt (arrow bool nnrat)]
           ['hd-alt (dual-feasible 'y-alt)]]
          (function/app
           (function/const* 'nnrat/lp-dual-optimality-certificate [zero-level])
           bool bool A bvec cvec xvec yvec rows cols hp hd hgap
           'y-alt 'hd-alt))
         optimal-pair
         (conjoin primal-optimal dual-optimal
                  primal-optimal-proof dual-optimal-proof)
         gap-and-optimality
         (conjoin
          (equiv (cdotx xvec) (bdoty yvec))
          (proposition/conjunction primal-optimal dual-optimal)
          hgap optimal-pair)
         dual-through-optimality
         (conjoin
          (dual-feasible yvec)
          (proposition/conjunction
           (equiv (cdotx xvec) (bdoty yvec))
           (proposition/conjunction primal-optimal dual-optimal))
          hd gap-and-optimality)]
     (conjoin
      (primal-feasible xvec)
      (proposition/conjunction
       (dual-feasible yvec)
       (proposition/conjunction
        (equiv (cdotx xvec) (bdoty yvec))
        (proposition/conjunction primal-optimal dual-optimal)))
      hp dual-through-optimality))})

(def definition-specs [])
(def theorem-specs [strong-duality-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.lp-optimality])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-lp-strong-duality theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.lp-strong-duality))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
