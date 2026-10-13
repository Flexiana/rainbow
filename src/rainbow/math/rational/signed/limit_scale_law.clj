(ns rainbow.math.rational.signed.limit-scale-law
  "Scalar multiple of a limit -- the missing piece of limit linearity.

  `analysis/limit-sum`, `-difference`, `-negate`, `-const` are already proved; this
  module adds the scaling law: if s converges to L with modulus M, then the sequence
  n |-> c * s n converges to c * L, for any POSITIVE rational c. Positivity is carried
  structurally by presenting c as `nnrat/make (succ p) q` (numerator succ p >= 1), which
  also makes the reciprocal well-behaved with no c=0 split.

  Proof route (smul-native, matching the band lane's `smul (from-nnrat c)` scaling):
  the modulus is rescaled by 1/c, `analysis/scaled-sequence-close-to-scaled-limit`
  gives the band at radius `c * (1/c) * eps`, and the supporting lemma
  `analysis/scale-reciprocal-radius-cancel` collapses that radius to `eps` up to signed
  equivalence (via multiply-associative, from-nnrat-multiply, divide-self-positive,
  multiply-one-left), after which `analysis/close-respects-radius-equivalence` rewrites
  the band's radius. Axiom-free; additive; does not touch the LP checker.

  Env chain: signed-limit-scalar-laws (band + converges/close), signed-limit-arithmetic
  (close-respects-radius-equivalence), signed-multiply-associative, signed-geometric-bridge
  (from-nnrat-multiply + rational division / reciprocal / unit laws)."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-scalar-laws :as scalar-laws]
            [rainbow.math.rational.signed.limit-arithmetic :as limit-arithmetic]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.geometric-bridge :as geometric-bridge]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-seq (function/arrow nat signed))
(def ^:private modulus (function/arrow signed nat))
(def ^:private nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & a] (apply function/app f a))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- fnn [x] (app (function/const* 'signed/from-nnrat []) x))
(defn- rmul [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- recip [x] (app (function/const* 'nnrat/reciprocal []) x))
(defn- mk [p q] (app (function/const* 'nnrat/make []) p q))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- strans [a b d h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b d h1 h2))
(defn- ssym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- massoc [a b d] (app (function/const* 'signed/multiply-associative []) a b d))
(defn- fmul [a b] (app (function/const* 'signed/from-nnrat-multiply []) a b))
(defn- mrre [a b x h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b x h))
(defn- fnnre [a b h] (app (function/const* 'signed/from-nnrat-respects-equivalence []) a b h))
(defn- dsp [p q] (app (function/const* 'nnrat/divide-self-positive []) p q))
(defn- mone [x] (app (function/const* 'signed/multiply-one-left []) x))
(defn- converges [s L M] (app (function/const* 'analysis/converges []) s L M))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- band [cc s L M conv eps n large]
  (app (function/const* 'analysis/scaled-sequence-close-to-scaled-limit []) cc s L M conv eps n large))
(defn- crre [L r1 r2 x h cl]
  (app (function/const* 'analysis/close-respects-radius-equivalence []) L r1 r2 x h cl))

;; ---- radius cancellation: (from-nnrat c) * ((from-nnrat (1/c)) * d) ~ d, c = (succ p)/q
(def scale-reciprocal-radius-cancel-spec
  {:name 'analysis/scale-reciprocal-radius-cancel
   :universes []
   :type (function/forall [['p nat] ['q nat] ['d signed]]
                          (let [cc (mk (succ 'p) 'q) rc (recip cc)]
                            (seqv (smul (fnn cc) (smul (fnn rc) 'd)) 'd)))
   :value
   (function/lam [['p nat] ['q nat] ['d signed]]
                 (let [cc (mk (succ 'p) 'q) rc (recip cc) fc (fnn cc) frc (fnn rc)
                       T0 (smul fc (smul frc 'd))
                       T1 (smul (smul fc frc) 'd)
                       T2 (smul (fnn (rmul cc rc)) 'd)
                       T3 (smul (fnn nnrat-one) 'd)
                       s1 (ssym T1 T0 (massoc fc frc 'd))
                       s2 (mrre (smul fc frc) (fnn (rmul cc rc)) 'd (fmul cc rc))
                       s3 (mrre (fnn (rmul cc rc)) (fnn nnrat-one) 'd (fnnre (rmul cc rc) nnrat-one (dsp 'p 'q)))
                       s4 (mone 'd)]
                   (strans T0 T1 'd s1
                           (strans T1 T2 'd s2
                                   (strans T2 T3 'd s3 s4)))))})

;; ---- limit-scale: n |-> c * s n converges to c * L, c = (succ p)/q, modulus rescaled by 1/c
(def limit-scale-spec
  {:name 'analysis/limit-scale
   :universes []
   :type (function/forall
          [['p nat] ['q nat] ['s sig-seq] ['L signed] ['M modulus] ['conv (converges 's 'L 'M)]]
          (let [cc (mk (succ 'p) 'q) fc (fnn cc) frc (fnn (recip cc))]
            (converges (function/lam [['n nat]] (smul fc (app 's 'n)))
                       (smul fc 'L)
                       (function/lam [['eps signed]] (app 'M (smul frc 'eps))))))
   :value
   (function/lam
    [['p nat] ['q nat] ['s sig-seq] ['L signed] ['M modulus] ['conv (converges 's 'L 'M)]]
    (let [cc (mk (succ 'p) 'q) fc (fnn cc) frc (fnn (recip cc))]
      (function/lam
       [['eps signed] ['n nat] ['hn (nat-le (app 'M (smul frc 'eps)) 'n)]]
       (let [b (band cc 's 'L 'M 'conv (smul frc 'eps) 'n 'hn)
             cn (app (function/const* 'analysis/scale-reciprocal-radius-cancel []) 'p 'q 'eps)]
         (crre (smul fc 'L) (smul fc (smul frc 'eps)) 'eps (smul fc (app 's 'n)) cn b)))))})

(def theorem-specs [scale-reciprocal-radius-cancel-spec limit-scale-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      scalar-laws/extend-environment
      limit-arithmetic/extend-environment
      multiply-associative/extend-environment
      geometric-bridge/extend-environment
      (support/extend-with :signed-limit-scale-law theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
