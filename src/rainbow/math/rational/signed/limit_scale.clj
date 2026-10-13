(ns rainbow.math.rational.signed.limit-scale
  "Axiom-free nonnegative scaling of signed-rational order bands.

  The convergence predicate installed by signed-convergence quantifies over all
  signed radii.  Consequently a constant sequence cannot inhabit it: at radius
  -1 its band would require 1 <= 0.  The reusable local law below is the strongest
  non-vacuous scaling result available without changing that predicate or adding
  signed division:

    close L e x -> close ((from-nnrat c) * L)
                         ((from-nnrat c) * e)
                         ((from-nnrat c) * x).

  Multiplication by the nonnegative Grothendieck pair (c,0) preserves signed
  order.  The proof reduces the signed comparison to nnrat/multiply-monotone and
  transports through distributivity and the nnrat zero laws."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.distributive :as distributive]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
            [rainbow.math.rational.nnrat.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.limit-arithmetic :as arithmetic]
            [rainbow.math.rational.signed.multiply :as signed-multiply]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- from-nnrat [v] (app (function/const* 'signed/from-nnrat []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- rmul [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- rat-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- rat-at-most [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- signed-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- close [L eps x] (app (function/const* 'analysis/close []) L eps x))

(defn- rat-refl [v]
  (app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- rat-trans [a b c first-step second-step]
  (app (function/const* 'nnrat/equivalent-transitive [])
       a b c first-step second-step))
(defn- rat-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       a ah b bh same-a same-b))
(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- rat-multiply-monotone [c a b ordered]
  (app (function/const* 'nnrat/multiply-monotone []) c a b ordered))
(defn- rat-multiply-commutative [a b]
  (app (function/const* 'nnrat/multiply-commutative []) a b))
(defn- rat-distributes-right [a b c]
  (app (function/const* 'nnrat/multiply-distributes-add-right []) a b c))
(defn- rat-multiply-zero-left [v]
  (app (function/const* 'nnrat/multiply-zero-left []) v))
(defn- rat-add-zero-right [v]
  (app (function/const* 'nnrat/add-zero-right []) v))

(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))

(defn- conjunction [a b]
  (app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- prop-left [a b both]
  (app (function/const* 'proposition/left []) a b both))
(defn- prop-right [a b both]
  (app (function/const* 'proposition/right []) a b both))

;; The positive/negative component of (from-nnrat c) * (p,n).
(defn- scaled-component [c p n]
  (radd (rmul c p) (rmul nnrat-zero n)))

;; c*(a+b) ~ c*a+c*b, obtained from the installed right-distributive law.
(defn- multiply-distributes-add-left [c a b]
  (let [left (rmul c (radd a b))
        commuted (rmul (radd a b) c)
        right-handed (radd (rmul a c) (rmul b c))
        right (radd (rmul c a) (rmul c b))]
    (rat-trans
     left commuted right
     (rat-multiply-commutative c (radd a b))
     (rat-trans
      commuted right-handed right
      (rat-distributes-right a b c)
      (rat-add-respects
       (rmul a c) (rmul c a) (rmul b c) (rmul c b)
       (rat-multiply-commutative a c)
       (rat-multiply-commutative b c))))))

;; c*p + 0*n ~ c*p.
(defn- scaled-component-drop-zero [c p n]
  (let [start (scaled-component c p n)
        middle (radd (rmul c p) nnrat-zero)
        finish (rmul c p)]
    (rat-trans
     start middle finish
     (rat-add-respects
      (rmul c p) (rmul c p) (rmul nnrat-zero n) nnrat-zero
      (rat-refl (rmul c p)) (rat-multiply-zero-left n))
     (rat-add-zero-right (rmul c p)))))

;; Scaling a componentwise sum agrees with summing the scaled components.
(defn- scaled-component-sum [c ap an bp bn]
  (let [source (scaled-component c (radd ap bp) (radd an bn))
        distributed (radd (rmul c ap) (rmul c bp))
        target (radd (scaled-component c ap an)
                     (scaled-component c bp bn))
        source-to-distributed
        (rat-trans
         source (rmul c (radd ap bp)) distributed
         (scaled-component-drop-zero c (radd ap bp) (radd an bn))
         (multiply-distributes-add-left c ap bp))
        target-to-distributed
        (rat-add-respects
         (scaled-component c ap an) (rmul c ap)
         (scaled-component c bp bn) (rmul c bp)
         (scaled-component-drop-zero c ap an)
         (scaled-component-drop-zero c bp bn))]
    (rat-trans source distributed target
               source-to-distributed
               (rat-sym target distributed target-to-distributed))))

;; Componentwise equivalence implies Grothendieck-pair equivalence.
(defn- signed-components-equivalent [left right positive-same negative-same]
  (rat-add-respects
   (pos left) (pos right) (neg right) (neg left)
   positive-same
   (rat-sym (neg left) (neg right) negative-same)))

(defn- multiply-from-nnrat-distributes-add [c a b]
  (let [k (from-nnrat c)
        left (smul k (sadd a b))
        right (sadd (smul k a) (smul k b))]
    (signed-components-equivalent
     left right
     (scaled-component-sum c (pos a) (neg a) (pos b) (neg b))
     (scaled-component-sum c (neg a) (pos a) (neg b) (pos b)))))

(defn- multiply-from-nnrat-distributes-subtract [c a b]
  (let [k (from-nnrat c)
        left (smul k (ssub a b))
        right (ssub (smul k a) (smul k b))]
    (signed-components-equivalent
     left right
     (scaled-component-sum c (pos a) (neg a) (neg b) (pos b))
     (scaled-component-sum c (neg a) (pos a) (pos b) (neg b)))))

;; The signed-order left/right component sum normalizes to c*(p+q).
(defn- scaled-order-side [c p p-zero q q-zero]
  (let [source (scaled-component c (radd p q) (radd p-zero q-zero))
        goal (radd (scaled-component c p p-zero)
                   (scaled-component c q q-zero))
        core (rmul c (radd p q))]
    (rat-trans
     goal source core
     (rat-sym source goal
              (scaled-component-sum c p p-zero q q-zero))
     (scaled-component-drop-zero c (radd p q) (radd p-zero q-zero)))))

(defn- multiply-from-nnrat-monotone [c a b ordered]
  (let [k (from-nnrat c)
        ka (smul k a) kb (smul k b)
        original-left (radd (pos a) (neg b))
        original-right (radd (pos b) (neg a))
        scaled-left (rmul c original-left)
        scaled-right (rmul c original-right)
        lifted (rat-multiply-monotone c original-left original-right ordered)
        goal-left (radd (pos ka) (neg kb))
        goal-right (radd (pos kb) (neg ka))]
    (rat-at-most-respects
     goal-left scaled-left goal-right scaled-right
     (scaled-order-side c (pos a) (neg a) (neg b) (pos b))
     (scaled-order-side c (pos b) (neg b) (neg a) (pos a))
     lifted)))

(def close-scale-nonnegative-spec
  {:name 'analysis/close-scale-nonnegative :universes []
   :type
   (function/forall
    [['c nnrat] ['L signed] ['eps signed] ['x signed]
     ['bounded (close 'L 'eps 'x)]]
    (close (smul (from-nnrat 'c) 'L)
           (smul (from-nnrat 'c) 'eps)
           (smul (from-nnrat 'c) 'x)))
   :value
   (function/lam
    [['c nnrat] ['L signed] ['eps signed] ['x signed]
     ['bounded (close 'L 'eps 'x)]]
    (let [k (from-nnrat 'c)
          low (ssub 'L 'eps) high (sadd 'L 'eps)
          scaled-L (smul k 'L) scaled-eps (smul k 'eps)
          scaled-x (smul k 'x)
          scaled-low (smul k low) scaled-high (smul k high)
          goal-low (ssub scaled-L scaled-eps)
          goal-high (sadd scaled-L scaled-eps)
          low<=x (prop-left (sle low 'x) (sle 'x high) 'bounded)
          x<=high (prop-right (sle low 'x) (sle 'x high) 'bounded)
          scaled-low<=x
          (multiply-from-nnrat-monotone 'c low 'x low<=x)
          x<=scaled-high
          (multiply-from-nnrat-monotone 'c 'x high x<=high)
          low-same
          (multiply-from-nnrat-distributes-subtract 'c 'L 'eps)
          high-same
          (multiply-from-nnrat-distributes-add 'c 'L 'eps)
          goal-low<=x
          (signed-at-most-respects
           scaled-low goal-low scaled-x scaled-x
           low-same (signed-refl scaled-x) scaled-low<=x)
          x<=goal-high
          (signed-at-most-respects
           scaled-x scaled-x scaled-high goal-high
           (signed-refl scaled-x) high-same x<=scaled-high)]
      (conjoin (sle goal-low scaled-x) (sle scaled-x goal-high)
               goal-low<=x x<=goal-high)))})

(def definition-specs [])
(def dependency-specs
  [distributive/multiply-distributes-add-right-spec])
(def theorem-specs [close-scale-nonnegative-spec])

;; Import only distributivity: the full provider also bundles an older
;; multiply-one-left declaration that conflicts with the arithmetic chain.
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (let [base (-> checked-environment arithmetic/extend-environment multiply-monotone/extend-environment multiply-commute/extend-environment signed-multiply/extend-environment)] (support/extend-with base :signed-limit-scale (concat dependency-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.limit-scale))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment (concat dependency-specs theorem-specs)))
