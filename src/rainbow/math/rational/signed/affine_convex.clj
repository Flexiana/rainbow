(ns rainbow.math.rational.signed.affine-convex
  "Affine functions are convex (indeed the convexity inequality is an equality) -- the
  first substantive instance of signed/convex-on, and the fact that makes linear/affine LP
  objectives convex (KKT/Lagrangian relevance).

    signed/affine-convex : forall a b, convex-on (x |-> a*x + b)

  For weights w0+w1~1: a*((w0)x+(w1)y)+b  ~  (w0)(a*x+b) + (w1)(a*y+b), an EQUALITY, so
  <= holds by reflexivity. Both sides expand (multiply-distributes-add-left), the scalar
  reassociates a*(W*v) ~ W*(a*v) (multiply assoc + comm), the constant term collapses
  (w0)b+(w1)b ~ b, and the four summands reorder (add-four-reorder). Off the magnitude/
  reciprocal modulus (no reduction wall). Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convex-function :as convex-fn]
            [rainbow.math.linear.matrix.action-scale :as action-scale]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.linear.matrix.affine-general-rate-certificate :as from-add]
            [rainbow.math.rational.signed.geometric-bridge :as geo-bridge]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.order-respects :as order-respects]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- mult-assoc [a b c] (app (function/const* 'signed/multiply-associative []) a b c))
(defn- mult-comm [a b] (app (function/const* 'signed/multiply-commutative []) a b))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- dist-add-left [f l r] (app (function/const* 'signed/multiply-distributes-add-left []) f l r))
(defn- dist-add-right [a b m] (app (function/const* 'signed/multiply-distributes-add-right []) a b m))
(defn- add-resp [a ah b bh ha hb] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh ha hb))
(defn- add-four [a b c d] (app (function/const* 'signed/add-four-reorder []) a b c d))
(defn- fnn-add [a b] (app (function/const* 'signed/from-nnrat-add []) a b))
(defn- fnn-resp [a b h] (app (function/const* 'signed/from-nnrat-respects-equivalence []) a b h))
(defn- one-left [z] (app (function/const* 'signed/multiply-one-left []) z))
(defn- le-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- convex-on [f] (app (function/const* 'signed/convex-on []) f))

;; a*(W*v) ~ W*(a*v)
(defn- swap-scalar [a W v]
  (eqv-tr (smul a (smul W v)) (smul (smul W a) v) (smul W (smul a v))
          (eqv-tr (smul a (smul W v)) (smul (smul a W) v) (smul (smul W a) v)
                  (eqv-sym (smul (smul a W) v) (smul a (smul W v)) (mult-assoc a W v))
                  (mrre (smul a W) (smul W a) v (mult-comm a W)))
          (mult-assoc W a v)))

;; (w0)B + (w1)B ~ B  given w0+w1 ~ 1
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

(def affine-convex-spec
  {:name 'signed/affine-convex
   :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (convex-on (function/lam [['x signed]] (sadd (smul 'a 'x) 'b))))
   :value
   (function/lam
    [['a signed] ['b signed]]
    (function/lam
     [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
      ['hw (nn-equiv (radd 'w0 'w1) rone)]]
     (let [W0 (fnn 'w0) W1 (fnn 'w1)
           wsum (sadd (smul W0 'x) (smul W1 'y))
           P0 (smul 'a (smul W0 'x)) P1 (smul 'a (smul W1 'y))
           Q0 (smul W0 (smul 'a 'x)) Q1 (smul W1 (smul 'a 'y))
           Wb0 (smul W0 'b) Wb1 (smul W1 'b)
           mid (sadd (sadd Q0 Wb0) (sadd Q1 Wb1))
           lhs (sadd (smul 'a wsum) 'b)
           rhs (sadd (smul W0 (sadd (smul 'a 'x) 'b)) (smul W1 (sadd (smul 'a 'y) 'b)))
           ;; LHS ~ mid
           lhs-mid
           (eqv-tr lhs (sadd (sadd P0 P1) 'b) mid
                   (add-resp (smul 'a wsum) (sadd P0 P1) 'b 'b
                             (dist-add-left 'a (smul W0 'x) (smul W1 'y)) (erefl 'b))
                   (eqv-tr (sadd (sadd P0 P1) 'b) (sadd (sadd Q0 Q1) 'b) mid
                           (add-resp (sadd P0 P1) (sadd Q0 Q1) 'b 'b
                                     (add-resp P0 Q0 P1 Q1 (swap-scalar 'a W0 'x) (swap-scalar 'a W1 'y))
                                     (erefl 'b))
                           (eqv-tr (sadd (sadd Q0 Q1) 'b) (sadd (sadd Q0 Q1) (sadd Wb0 Wb1)) mid
                                   (add-resp (sadd Q0 Q1) (sadd Q0 Q1) 'b (sadd Wb0 Wb1)
                                             (erefl (sadd Q0 Q1))
                                             (eqv-sym (sadd Wb0 Wb1) 'b (weights-collapse 'w0 'w1 'b 'hw)))
                                   (add-four Q0 Q1 Wb0 Wb1))))
           ;; RHS ~ mid
           rhs-mid
           (add-resp (smul W0 (sadd (smul 'a 'x) 'b)) (sadd Q0 Wb0)
                     (smul W1 (sadd (smul 'a 'y) 'b)) (sadd Q1 Wb1)
                     (dist-add-left W0 (smul 'a 'x) 'b) (dist-add-left W1 (smul 'a 'y) 'b))
           lhs-rhs (eqv-tr lhs mid rhs lhs-mid (eqv-sym rhs mid rhs-mid))]
       (le-resp lhs lhs lhs rhs (erefl lhs) lhs-rhs (le-refl lhs)))))})

(def theorem-specs [affine-convex-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      convex-fn/extend-environment
      action-scale/extend-environment
      distributive/extend-environment
      multiply-associative/extend-environment
      multiply-ring/extend-environment
      map-sum/extend-environment
      from-add/extend-environment
      geo-bridge/extend-environment
      unit-laws/extend-environment
      order-transitivity/extend-environment
      order-respects/extend-environment
      (support/extend-with :signed-affine-convex theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
