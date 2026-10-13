(ns rainbow.math.rational.signed.inverse-unique
  "B6f lever (replaces the awkward multiply-right-cancel): uniqueness of multiplicative
  inverse.

    signed/inverse-unique : u * w ~ 1 -> v * w ~ 1 -> u ~ v

  Pure field algebra, no positivity hypothesis: u ~ u*1 ~ u*(w*v) ~ (u*w)*v ~ 1*v ~ v.
  Signed rationals have no strict order in the corpus, so a strict multiply-right-cancel
  (a*c<=b*c, 0<c -> a<=b) is awkward to state and needs antisymmetry + equivalence-cancel;
  inverse-unique is the clean substitute the limit-reciprocal assembly actually needs:
  |1/(s n)|*|s n| ~ 1 (absolute-reciprocal-times-self) and reciprocal|s n|*|s n| ~ 1
  (multiply-reciprocal-self) give |1/(s n)| ~ reciprocal|s n|, then reciprocal-antitone
  supplies the constant bound |1/(s n)| <= reciprocal(|L|/2) = 2/|L|. Axiom-free; additive;
  does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence-laws]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private one (function/const* 'signed/one []))
(defn- app [f & a] (apply function/app f a))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- mult-comm [a b] (app (function/const* 'signed/multiply-commutative []) a b))
(defn- mult-assoc [a b c] (app (function/const* 'signed/multiply-associative []) a b c))
(defn- mlre [b bh c h] (app (function/const* 'signed/multiply-left-respects-equivalence []) b bh c h))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- one-left [z] (app (function/const* 'signed/multiply-one-left []) z))

(def inverse-unique-spec
  {:name 'signed/inverse-unique
   :universes []
   :type (function/forall
          [['u signed] ['v signed] ['w signed]
           ['hu (seqv (smul 'u 'w) one)] ['hv (seqv (smul 'v 'w) one)]]
          (seqv 'u 'v))
   :value
   (function/lam
    [['u signed] ['v signed] ['w signed]
     ['hu (seqv (smul 'u 'w) one)] ['hv (seqv (smul 'v 'w) one)]]
    (let [;; u*1 ~ u  (commute + one-left), then u ~ u*1
          one-right-u (eqv-tr (smul 'u one) (smul one 'u) 'u (mult-comm 'u one) (one-left 'u))
          u-u1 (eqv-sym (smul 'u one) 'u one-right-u)
          ;; 1 ~ w*v   (from v*w~1)
          one-wv (eqv-tr one (smul 'v 'w) (smul 'w 'v)
                          (eqv-sym (smul 'v 'w) one 'hv) (mult-comm 'v 'w))
          ;; u*1 ~ u*(w*v)
          s2 (mlre one (smul 'w 'v) 'u one-wv)
          ;; u*(w*v) ~ (u*w)*v
          s3 (eqv-sym (smul (smul 'u 'w) 'v) (smul 'u (smul 'w 'v)) (mult-assoc 'u 'w 'v))
          ;; (u*w)*v ~ 1*v
          s4 (mrre (smul 'u 'w) one 'v 'hu)
          ;; 1*v ~ v
          s5 (one-left 'v)]
      (eqv-tr 'u (smul 'u one) 'v u-u1
              (eqv-tr (smul 'u one) (smul 'u (smul 'w 'v)) 'v s2
                      (eqv-tr (smul 'u (smul 'w 'v)) (smul (smul 'u 'w) 'v) 'v s3
                              (eqv-tr (smul (smul 'u 'w) 'v) (smul one 'v) 'v s4 s5))))))})

(def theorem-specs [inverse-unique-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      multiply-ring/extend-environment
      multiply-associative/extend-environment
      unit-laws/extend-environment
      equivalence-laws/extend-environment
      (support/extend-with :signed-inverse-unique theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
