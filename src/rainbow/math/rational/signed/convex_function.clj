(ns rainbow.math.rational.signed.convex-function
  "The two-point convex-function representation over signed rationals, and its first
  witnesses -- the base for Jensen's inequality and for connecting convexity to the
  KKT / Lagrangian optimization lane.

    signed/convex-on f  :=  for all nnrat weights w0,w1 with w0+w1~1 and signed x,y,
                            f((w0)x + (w1)y) <= (w0) f(x) + (w1) f(y)
      (weights injected by from-nnrat; the combination is the same as signed/convex-*).
    signed/identity-convex : convex-on (x |-> x)         -- trivial (equality, reflexive)
    signed/constant-convex : convex-on (x |-> c)         -- via the weight-sum collapse

  identity: both sides reduce to the same combination, so at-most-reflexive closes it.
  constant: f collapses each side to c, and (w0)c + (w1)c ~ (w0+w1)c ~ 1*c ~ c via
  distributes-add-right + from-nnrat-add + (w0+w1~1) + multiply-one-left. Off the
  magnitude/reciprocal modulus (no reduction wall). Next: affine and square convexity
  (the variance inequality), then n-point Jensen by induction. Axiom-free; additive;
  does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.affine-general-rate-certificate :as from-add]
            [rainbow.math.rational.signed.geometric-bridge :as geo-bridge]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.order-respects :as order-respects]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-fn (function/arrow signed signed))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- wsum [w0 w1 a b] (sadd (smul (fnn w0) a) (smul (fnn w1) b)))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- dist-add-right [a b m] (app (function/const* 'signed/multiply-distributes-add-right []) a b m))
(defn- fnn-add [a b] (app (function/const* 'signed/from-nnrat-add []) a b))
(defn- fnn-resp [a b h] (app (function/const* 'signed/from-nnrat-respects-equivalence []) a b h))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- one-left [z] (app (function/const* 'signed/multiply-one-left []) z))
(defn- le-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- convex-on [f] (app (function/const* 'signed/convex-on []) f))

;; (w0)B + (w1)B ~ B given w0+w1 ~ 1
(defn- weights-collapse [w0 w1 B hw]
  (eqv-tr (sadd (smul (fnn w0) B) (smul (fnn w1) B)) (smul (fnn (radd w0 w1)) B) B
          (eqv-tr (sadd (smul (fnn w0) B) (smul (fnn w1) B))
                  (smul (sadd (fnn w0) (fnn w1)) B) (smul (fnn (radd w0 w1)) B)
                  (eqv-sym (smul (sadd (fnn w0) (fnn w1)) B)
                           (sadd (smul (fnn w0) B) (smul (fnn w1) B))
                           (dist-add-right (fnn w0) (fnn w1) B))
                  (mrre (sadd (fnn w0) (fnn w1)) (fnn (radd w0 w1)) B (fnn-add w0 w1)))
          (eqv-tr (smul (fnn (radd w0 w1)) B) (smul (fnn rone) B) B
                  (mrre (fnn (radd w0 w1)) (fnn rone) B (fnn-resp (radd w0 w1) rone hw))
                  (one-left B))))

(def convex-on-spec
  {:name 'signed/convex-on
   :kind :definition
   :transparency :reducible
   :universes []
   :type (function/arrow sig-fn 'Prop)
   :value
   (function/lam
    [['f sig-fn]]
    (function/forall
     [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
      ['hw (nn-equiv (radd 'w0 'w1) rone)]]
     (sle (app 'f (wsum 'w0 'w1 'x 'y))
          (wsum 'w0 'w1 (app 'f 'x) (app 'f 'y)))))})

(def identity-convex-spec
  {:name 'signed/identity-convex
   :universes []
   :type (convex-on (function/lam [['x signed]] 'x))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
     ['hw (nn-equiv (radd 'w0 'w1) rone)]]
    (le-refl (wsum 'w0 'w1 'x 'y)))})

(def constant-convex-spec
  {:name 'signed/constant-convex
   :universes []
   :type (function/forall [['c signed]] (convex-on (function/lam [['x signed]] 'c)))
   :value
   (function/lam
    [['c signed]]
    (function/lam
     [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
      ['hw (nn-equiv (radd 'w0 'w1) rone)]]
     ;; goal: sle c ((w0)c + (w1)c); RHS ~ c, so c <= RHS by reflexive + respects
     (le-resp 'c 'c 'c (wsum 'w0 'w1 'c 'c)
              (erefl 'c)
              (eqv-sym (wsum 'w0 'w1 'c 'c) 'c (weights-collapse 'w0 'w1 'c 'hw))
              (le-refl 'c))))})

(def theorem-specs [convex-on-spec identity-convex-spec constant-convex-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      distributive/extend-environment
      from-add/extend-environment
      geo-bridge/extend-environment
      unit-laws/extend-environment
      multiply-ring/extend-environment
      order-transitivity/extend-environment
      order-respects/extend-environment
      (support/extend-with :signed-convex-function theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
