(ns rainbow.math.rational.signed.close-radius-monotone
  "Band weakening: a closeness band only widens with its radius.
  analysis/close-radius-monotone : close L r x -> r <= r' -> close L r' x.
  From close = (L-r<=x) AND (x<=L+r): L-r'<=L-r<=x (negate-reverses-order + add-monotone)
  and x<=L+r<=L+r' (add-monotone). Axiom-free; additive. A generally useful analysis
  lemma (and the >=-relaxation the limit-product assembly wants)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convergence :as convergence]
            [rainbow.math.rational.signed.absolute-sign :as absolute-sign]
            [rainbow.math.rational.signed.distance-triangle :as distance-triangle]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- neg* [x] (app (function/const* 'signed/negate []) x))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- close* [L e x] (app (function/const* 'analysis/close []) L e x))
(defn- le-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- le-tr [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- add-mono [a b c d h1 h2] (app (function/const* 'signed/add-monotone []) a b c d h1 h2))
(defn- neg-rev [a b h] (app (function/const* 'signed/negate-reverses-order []) a b h))
(defn- p-left [P Q h] (app (function/const* 'proposition/left []) P Q h))
(defn- p-right [P Q h] (app (function/const* 'proposition/right []) P Q h))
(defn- conjoin [P Q p q] (app (function/const* 'proposition/conjoin []) P Q p q))

(def close-radius-monotone-spec
  {:name 'analysis/close-radius-monotone
   :universes []
   :type (function/forall
          [['L signed] ['r signed] ['x signed] ['r2 signed]
           ['hc (close* 'L 'r 'x)] ['hr (sle 'r 'r2)]]
          (close* 'L 'r2 'x))
   :value
   (function/lam
    [['L signed] ['r signed] ['x signed] ['r2 signed]
     ['hc (close* 'L 'r 'x)] ['hr (sle 'r 'r2)]]
    (let [P (sle (ssub 'L 'r) 'x)                 ; L - r <= x
          Q (sle 'x (sadd 'L 'r))                 ; x <= L + r
          lo (p-left P Q 'hc)                     ; L - r <= x
          hi (p-right P Q 'hc)                    ; x <= L + r
          ;; L - r2 <= L - r : from -r2 <= -r (negate-reverses-order) + add-monotone on L
          nrr (neg-rev 'r 'r2 'hr)                ; -r2 <= -r
          losub (add-mono 'L 'L (neg* 'r2) (neg* 'r) (le-refl 'L) nrr)  ; (L + -r2) <= (L + -r) ; defeq (L-r2)<=(L-r)
          lo2 (le-tr (ssub 'L 'r2) (ssub 'L 'r) 'x losub lo)            ; L - r2 <= x
          ;; L + r <= L + r2
          hisub (add-mono 'L 'L 'r 'r2 (le-refl 'L) 'hr)               ; (L + r) <= (L + r2)
          hi2 (le-tr 'x (sadd 'L 'r) (sadd 'L 'r2) hi hisub)]          ; x <= L + r2
      (conjoin (sle (ssub 'L 'r2) 'x) (sle 'x (sadd 'L 'r2)) lo2 hi2)))})

(def theorem-specs [close-radius-monotone-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.convergence rainbow.math.rational.signed.absolute-sign rainbow.math.rational.signed.distance-triangle])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-close-radius-monotone theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.close-radius-monotone))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
