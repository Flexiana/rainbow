(ns rainbow.math.rational.signed.rate-order
  "Order closure under vanishing signed-rational error bounds.

  The Archimedean theorem turns `x <= y + 1/(k+1)` for every natural k into
  `x <= y`. Its rate-null corollary accepts any nonnegative signed error
  sequence with an explicit modulus. These are reusable limit/order lemmas;
  they do not assume completeness or construct limits.

  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.bellman-signed-value-iteration-general-converges
             :as general-convergence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.additive-distance :as additive-distance]
            [rainbow.math.rational.signed.limit-uniqueness :as signed-limit]))

(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def nat-one (function/app (function/const* 'data/succ []) nat-zero))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- rmake [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make []) numerator denominator-predecessor))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- pos [value]
  (app (function/const* 'signed/positive []) value))
(defn- neg [value]
  (app (function/const* 'signed/negative []) value))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null []) sequence modulus))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def signed-at-most-of-all-plus-reciprocal-spec
  (let [reciprocal (fn [k] (rmake nat-one k))]
    {:name 'analysis/signed-at-most-of-all-plus-reciprocal
     :universes []
     :type
     (function/forall
      [['x signed] ['y signed]
       ['bounded
        (function/forall
         [['k nat]]
         (sle 'x (sadd 'y (from-nnrat (reciprocal 'k)))))] ]
      (sle 'x 'y))
     :value
     (function/lam
      [['x signed] ['y signed]
       ['bounded
        (function/forall
         [['k nat]]
         (sle 'x (sadd 'y (from-nnrat (reciprocal 'k)))))] ]
      (let [left-cross (radd (pos 'x) (neg 'y))
            right-cross (radd (pos 'y) (neg 'x))
            cross-bounded
            (function/lam
             [['k nat]]
             (let [radius (reciprocal 'k)
                   epsilon (from-nnrat radius)
                   difference-bound
                   (app
                    (function/const*
                     'signed/subtract-at-most-of-additive-upper [])
                    'x 'y epsilon (app 'bounded 'k))
                   premise-left (radd left-cross nnrat-zero)
                   premise-right
                   (radd radius (radd (neg 'x) (pos 'y)))
                   target-right (radd right-cross radius)]
               (app
                (function/const* 'nnrat/at-most-respects-equivalence [])
                left-cross premise-left target-right premise-right
                (app
                 (function/const* 'nnrat/equivalent-symmetric [])
                 premise-left left-cross
                 (app (function/const* 'nnrat/add-zero-right []) left-cross))
                (ring/equiv target-right premise-right)
                difference-bound)))]
        (app
         (function/const* 'nnrat/at-most-of-all-plus-reciprocal [])
         left-cross right-cross cross-bounded)))}))

(def signed-at-most-of-rate-null-upper-bounds-spec
  (let [sequence-type (function/arrow nat signed)
        modulus-type (function/arrow nat nat)
        reciprocal
        (fn [k]
          (from-nnrat
           (app (function/const* 'nnrat/harmonic []) k)))]
    {:name 'analysis/signed-at-most-of-rate-null-upper-bounds
     :universes []
     :type
     (function/forall
      [['error sequence-type]
       ['modulus modulus-type]
       ['x signed] ['y signed]
       ['null (signed-rate-null 'error 'modulus)]
       ['bounded
        (function/forall
         [['steps nat]]
         (sle 'x (sadd 'y (app 'error 'steps))))]]
      (sle 'x 'y))
     :value
     (function/lam
      [['error sequence-type]
       ['modulus modulus-type]
       ['x signed] ['y signed]
       ['null (signed-rate-null 'error 'modulus)]
       ['bounded
        (function/forall
         [['steps nat]]
         (sle 'x (sadd 'y (app 'error 'steps))))]]
      (app
       (function/const*
        'analysis/signed-at-most-of-all-plus-reciprocal [])
       'x 'y
       (function/lam
        [['k nat]]
        (let [steps (app 'modulus 'k)
              error-at (app 'error steps)
              radius (reciprocal 'k)
              null-at
              (app 'null 'k steps
                   (app (function/const* 'nat/at-most-reflexive []) steps))
              error-small
              (right-conjunct
               (sle signed-zero error-at) (sle error-at radius) null-at)
              sum-small
              (app (function/const* 'signed/add-monotone [])
                   'y 'y error-at radius
                   (app (function/const* 'signed/at-most-reflexive []) 'y)
                   error-small)]
          (order-transitive
           'x (sadd 'y error-at) (sadd 'y radius)
           (app 'bounded steps) sum-small)))))}))

(def definition-specs [])
(def theorem-specs
  [signed-at-most-of-all-plus-reciprocal-spec
   signed-at-most-of-rate-null-upper-bounds-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.bellman-signed-value-iteration-general-converges rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.additive-distance rainbow.math.rational.nnrat.ring])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :signed-rate-order theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.rate-order))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
