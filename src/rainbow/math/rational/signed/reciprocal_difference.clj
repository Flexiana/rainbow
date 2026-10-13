(ns rainbow.math.rational.signed.reciprocal-difference
  "The reciprocal-difference identity: the algebraic heart of the limit-reciprocal law.

    signed/reciprocal-difference :
      1 <= num(mag(a*a)) -> 1 <= num(mag(b*b)) ->
      (reciprocal a - reciprocal b) ~ (reciprocal a * reciprocal b) * (b - a)

  This turns a difference of reciprocals into a product with (b - a), so the distance
  d(1/(s n), 1/L) can be bounded by d(s n, L) times a factor -- the step that makes the
  reciprocal sequence's modulus computable. Pure signed-field algebra; no analysis.

  Proof: expand X*(b-a) = X*b - X*a (distributes-add-left + multiply-negate-right), with
  X = 1/a * 1/b; then X*b ~ 1/a (assoc, commute, b*(1/b)~1 via multiply-reciprocal-self,
  one laws) and X*a ~ 1/b symmetrically; subtract-respects assembles it. Axiom-free;
  additive; does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.reciprocal :as reciprocal]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.linear.matrix.action-scale :as action-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.linear.vector.dot-subtract :as dot-subtract]))

(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private zero (function/const* 'data/zero []))
(def ^:private one (function/const* 'signed/one []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sneg [a] (app (function/const* 'signed/negate []) a))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- recip [x] (app (function/const* 'signed/reciprocal []) x))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- pos-hyp [x] (nat-le (succ zero) (numr (mag (smul x x)))))
;; wrappers
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- mult-assoc [a b c] (app (function/const* 'signed/multiply-associative []) a b c))
(defn- mult-comm [a b] (app (function/const* 'signed/multiply-commutative []) a b))
(defn- mlre [b bh c h] (app (function/const* 'signed/multiply-left-respects-equivalence []) b bh c h))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- one-left [z] (app (function/const* 'signed/multiply-one-left []) z))
(defn- dist-add-left [f l r] (app (function/const* 'signed/multiply-distributes-add-left []) f l r))
(defn- neg-right [l r] (app (function/const* 'signed/multiply-negate-right []) l r))
(defn- add-resp [a ah b bh ha hb] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh ha hb))
(defn- sub-resp [a ah b bh ha hb] (app (function/const* 'signed/subtract-respects-equivalence []) a ah b bh ha hb))
(defn- self-inv [x h] (app (function/const* 'signed/multiply-reciprocal-self []) x h))
;; one-right : smul z one ~ z  (no native lemma; commute then one-left)
(defn- one-right [z] (eqv-tr (smul z one) (smul one z) z (mult-comm z one) (one-left z)))

(def reciprocal-difference-spec
  {:name 'signed/reciprocal-difference
   :universes []
   :type (function/forall
          [['a signed] ['b signed] ['ha (pos-hyp 'a)] ['hb (pos-hyp 'b)]]
          (seqv (ssub (recip 'a) (recip 'b))
                (smul (smul (recip 'a) (recip 'b)) (ssub 'b 'a))))
   :value
   (function/lam
    [['a signed] ['b signed] ['ha (pos-hyp 'a)] ['hb (pos-hyp 'b)]]
    (let [ra (recip 'a) rb (recip 'b)
          X (smul ra rb)
          Xb (smul X 'b) Xa (smul X 'a)
          ;; X*b ~ ra
          xb (eqv-tr Xb (smul ra (smul rb 'b)) ra
                     (mult-assoc ra rb 'b)
                     (eqv-tr (smul ra (smul rb 'b)) (smul ra (smul 'b rb)) ra
                             (mlre (smul rb 'b) (smul 'b rb) ra (mult-comm rb 'b))
                             (eqv-tr (smul ra (smul 'b rb)) (smul ra one) ra
                                     (mlre (smul 'b rb) one ra (self-inv 'b 'hb))
                                     (one-right ra))))
          ;; X*a ~ rb
          xa (eqv-tr Xa (smul (smul rb ra) 'a) rb
                     (mrre X (smul rb ra) 'a (mult-comm ra rb))
                     (eqv-tr (smul (smul rb ra) 'a) (smul rb (smul ra 'a)) rb
                             (mult-assoc rb ra 'a)
                             (eqv-tr (smul rb (smul ra 'a)) (smul rb one) rb
                                     (mlre (smul ra 'a) one rb
                                           (eqv-tr (smul ra 'a) (smul 'a ra) one
                                                   (mult-comm ra 'a) (self-inv 'a 'ha)))
                                     (one-right rb))))
          ;; X*(b-a) ~ X*b - X*a
          dist (eqv-tr (smul X (ssub 'b 'a))
                       (sadd Xb (smul X (sneg 'a)))
                       (ssub Xb Xa)
                       (dist-add-left X 'b (sneg 'a))
                       (add-resp Xb Xb (smul X (sneg 'a)) (sneg Xa)
                                 (erefl Xb) (neg-right X 'a)))
          ;; assemble:  X*(b-a) ~ Xb - Xa ~ ra - rb
          chain (eqv-tr (smul X (ssub 'b 'a)) (ssub Xb Xa) (ssub ra rb)
                        dist (sub-resp Xb ra Xa rb xb xa))]
      (eqv-sym (smul X (ssub 'b 'a)) (ssub ra rb) chain)))})

(def theorem-specs [reciprocal-difference-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      reciprocal/extend-environment
      unit-laws/extend-environment
      action-scale/extend-environment
      dot-negate/extend-environment
      map-sum/extend-environment
      dot-subtract/extend-environment
      (support/extend-with :signed-reciprocal-difference theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
