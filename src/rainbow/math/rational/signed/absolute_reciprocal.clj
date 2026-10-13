(ns rainbow.math.rational.signed.absolute-reciprocal
  "B5 of the limit-reciprocal arc: the absolute value of a reciprocal, kept through the
  SAME magnitude(x*x) representative (avoids the absent magnitude-respects / nnrat
  reciprocal-respects lemmas -- the nnrat-radius-cancel philosophy).

    signed/absolute-reciprocal :
      |reciprocal x| ~ |x| * (from-nnrat (recip mmag))
    where mmag = make (succ (pred (num (magnitude (x*x))))) (den-pred (magnitude (x*x))),
    so the RHS is exactly |x| * (1/(x*x)).

  Since reciprocal x = x * (1/(x*x)) and 1/(x*x) = from-nnrat(recip mmag) is nonnegative,
  |reciprocal x| = |x * (1/(x*x))| ~ |x| * |1/(x*x)| ~ |x| * (1/(x*x)) [absolute-multiply +
  absolute-of-nonnegative]. No nonzero hypothesis needed (holds structurally for all x).
  The assembly bounds 1/(x*x) via the antitone lemma applied to mag(x*x) directly, never
  forming reciprocal|x|. Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.reciprocal :as reciprocal]
            [rainbow.math.rational.signed.absolute-multiply :as absolute-multiply]
            [rainbow.math.rational.signed.absolute-sign :as absolute-sign]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- pred* [n] (app (function/const* 'nat/predecessor []) n))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denpred [x] (app (function/const* 'nnrat/denominator-predecessor []) x))
(defn- mk [num dp] (app (function/const* 'data/pair [tl tl]) nat nat num dp))
(defn- nrecip [x] (app (function/const* 'nnrat/reciprocal []) x))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- reciprocal [x] (app (function/const* 'signed/reciprocal []) x))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- abs-mul [a b] (app (function/const* 'signed/absolute-multiply []) a b))
(defn- abs-of-nn [w h] (app (function/const* 'signed/absolute-of-nonnegative []) w h))
(defn- mlre [b bh c h] (app (function/const* 'signed/multiply-left-respects-equivalence []) b bh c h))
(defn- zero-at-most [q] (app (function/const* 'nnrat/zero-at-most []) q))
(defn- zle-of-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))

(defn- rq-of [x] (nrecip (mk (succ (pred* (numr (mag (smul x x))))) (denpred (mag (smul x x))))))

(def absolute-reciprocal-spec
  {:name 'signed/absolute-reciprocal
   :universes []
   :type (function/forall [['x signed]]
                          (seqv (abs* (reciprocal 'x)) (smul (abs* 'x) (fnn (rq-of 'x)))))
   :value
   (function/lam [['x signed]]
                 (let [rq (rq-of 'x)
                       R (fnn rq)]
                   ;; |reciprocal x| = |x * R| ~ |x|*|R| ~ |x|*R
                   (eqv-tr (abs* (smul 'x R)) (smul (abs* 'x) (abs* R)) (smul (abs* 'x) R)
                           (abs-mul 'x R)
                           (mlre (abs* R) R (abs* 'x)
                                 (abs-of-nn R (zle-of-nn R (zero-at-most rq)))))))})

(def theorem-specs [absolute-reciprocal-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.reciprocal rainbow.math.rational.signed.absolute-multiply rainbow.math.rational.signed.absolute-sign rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.multiply-order rainbow.math.rational.nnrat.farkas-elim-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-absolute-reciprocal theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.absolute-reciprocal))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
