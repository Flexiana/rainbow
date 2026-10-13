(ns rainbow.math.rational.signed.multiply-monotone
  "Scaling a signed inequality by a nonnegative signed scalar.

      signed/multiply-left-monotone  : 0 <= c -> a <= b -> c*a <= c*b
      signed/multiply-right-monotone : 0 <= c -> a <= b -> a*c <= b*c

  This is the keystone the signed layer was missing: the additive toolkit could
  add an inequality to something, and the sign rules could decide the sign of a
  product, but nothing could SCALE an inequality -- which is what every weighted
  bound, gradient step, discounted backup and convexity argument does.

  The proof is `nnrat/rearrangement-two-point`, instantiated with the ORDER SUMS
  themselves rather than the components.  Signed order `a <= b` is the nnrat
  comparison `q0 <= m0` where q0 = Pa + Nb and m0 = Pb + Na, and `0 <= c` is
  `Nc <= Pc`.  Feeding (n,p,q,m) := (q0, m0, Nc, Pc) to rearrangement gives

      m0*Nc + q0*Pc  <=  m0*Pc + q0*Nc

  and each side is the corresponding side of the unfolded goal rearranged: the
  same four monomials, distributed and commuted.  Both of those rearrangements
  are now single `rainbow.math.rational.nnrat.ring` calls -- they were about a hundred
  lines of hand-chained four-reorders and per-product commutations before the
  tactic existed.

  Native and axiom-free; chains the nnrat rearrangement toolkit, the nnrat-ring
  tactic and the signed sign rules on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.order-difference :as difference]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.multiply-order :as sign]))

(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(def ^:private radd ring/radd)
(def ^:private rmul ring/rmul)
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))

(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- rearrange [n p q m hnp hqm]
  (app (function/const* 'nnrat/rearrangement-two-point []) n p q m hnp hqm))
(defn- nonneg-of-zero-at-most [x h]
  (app (function/const* 'signed/nonnegative-of-zero-at-most []) x h))

;; the two Grothendieck components of a signed product
(defn- product-positive [pl nl pr nr] (radd (rmul pl pr) (rmul nl nr)))
(defn- product-negative [pl nl pr nr] (radd (rmul pl nr) (rmul nl pr)))

(def multiply-left-monotone-spec
  {:name 'signed/multiply-left-monotone :universes []
   :type (function/forall
          [['c signed] ['a signed] ['b signed]
           ['hc (sle signed-zero 'c)]
           ['hab (sle 'a 'b)]]
          (sle (smul 'c 'a) (smul 'c 'b)))
   :value
   (function/lam
    [['c signed] ['a signed] ['b signed]
     ['hc (sle signed-zero 'c)]
     ['hab (sle 'a 'b)]]
    (let [Pc (pos 'c) Nc (neg 'c)
          Pa (pos 'a) Na (neg 'a)
          Pb (pos 'b) Nb (neg 'b)
          q0 (radd Pa Nb)
          m0 (radd Pb Na)
          ;; unfolded goal: positive (c*a) + negative (c*b)
          ;;             <= positive (c*b) + negative (c*a)
          goal-left (radd (product-positive Pc Nc Pa Na)
                          (product-negative Pc Nc Pb Nb))
          goal-right (radd (product-positive Pc Nc Pb Nb)
                           (product-negative Pc Nc Pa Na))
          raw-left (radd (rmul m0 Nc) (rmul q0 Pc))
          raw-right (radd (rmul m0 Pc) (rmul q0 Nc))]
      (rat-at-most-respects
       goal-left raw-left goal-right raw-right
       (ring/equiv goal-left raw-left)
       (ring/equiv goal-right raw-right)
       (rearrange q0 m0 Nc Pc 'hab (nonneg-of-zero-at-most 'c 'hc)))))})

;; The mirrored statement.  Signed multiplication commutes only up to reordering
;; the four component products, so this transports the left version through that
;; reordering -- again one tactic call per side.
(def multiply-right-monotone-spec
  {:name 'signed/multiply-right-monotone :universes []
   :type (function/forall
          [['c signed] ['a signed] ['b signed]
           ['hc (sle signed-zero 'c)]
           ['hab (sle 'a 'b)]]
          (sle (smul 'a 'c) (smul 'b 'c)))
   :value
   (function/lam
    [['c signed] ['a signed] ['b signed]
     ['hc (sle signed-zero 'c)]
     ['hab (sle 'a 'b)]]
    (let [Pc (pos 'c) Nc (neg 'c)
          Pa (pos 'a) Na (neg 'a)
          Pb (pos 'b) Nb (neg 'b)
          goal-left (radd (product-positive Pa Na Pc Nc)
                          (product-negative Pb Nb Pc Nc))
          goal-right (radd (product-positive Pb Nb Pc Nc)
                           (product-negative Pa Na Pc Nc))
          source-left (radd (product-positive Pc Nc Pa Na)
                            (product-negative Pc Nc Pb Nb))
          source-right (radd (product-positive Pc Nc Pb Nb)
                             (product-negative Pc Nc Pa Na))]
      (rat-at-most-respects
       goal-left source-left goal-right source-right
       (ring/equiv goal-left source-left)
       (ring/equiv goal-right source-right)
       (app (function/const* 'signed/multiply-left-monotone [])
            'c 'a 'b 'hc 'hab))))})

(def definition-specs [])
(def theorem-specs
  [multiply-left-monotone-spec multiply-right-monotone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ring/extend-environment
      difference/extend-environment
      sign/extend-environment
      (support/extend-with :signed-multiply-monotone theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
