(ns rainbow.math.rational.signed.limit-difference
  "The difference limit law for signed-rational sequences.

  `signed/subtract a b` and `signed/add a (signed/negate b)` are the *same*
  Grothendieck pair definitionally -- both reduce to

    make (positive a + negative b) (negative a + positive b)

  so subtraction needs no arithmetic of its own: the additive limit law applied
  to the negated sequence already has the subtractive type.  This module records
  that composition as first-class theorems, closing the signed limit-arithmetic
  layer (sum, scalar, negation, difference).

  Native and axiom-free; chains the D63 limit-arithmetic and limit-negation
  modules."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-arithmetic :as arithmetic]
            [rainbow.math.rational.signed.limit-negate :as negate]))

(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def sig-seq (function/arrow nat signed))
(def modulus (function/arrow signed nat))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sneg [v] (app (function/const* 'signed/negate []) v))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- close [L eps x] (app (function/const* 'analysis/close []) L eps x))
(defn- converges [s L M]
  (app (function/const* 'analysis/converges []) s L M))

(defn- close-negate [L eps x bounded]
  (app (function/const* 'analysis/close-negate []) L eps x bounded))
(defn- close-additive [L eps-left x M eps-right y x-close y-close]
  (app (function/const* 'analysis/close-additive [])
       L eps-left x M eps-right y x-close y-close))
(defn- limit-negate [s L M s-converges]
  (app (function/const* 'analysis/limit-negate []) s L M s-converges))
(defn- limit-sum [s t L M Ms Mt s-converges t-converges]
  (app (function/const* 'analysis/limit-sum [])
       s t L M Ms Mt s-converges t-converges))

;; Two bands subtract: the left band is kept, the right one is reflected by
;; `close-negate`, and `close-additive` combines them.  The additive conclusion
;; `close (L + -M) (eps-left + eps-right) (x + -y)` is definitionally the
;; subtractive band `close (L - M) (eps-left + eps-right) (x - y)`.
(def close-subtractive-spec
  {:name 'analysis/close-subtractive :universes []
   :type
   (function/forall
    [['L signed] ['eps-left signed] ['x signed]
     ['M signed] ['eps-right signed] ['y signed]
     ['x-close (close 'L 'eps-left 'x)]
     ['y-close (close 'M 'eps-right 'y)]]
    (close (ssub 'L 'M) (sadd 'eps-left 'eps-right) (ssub 'x 'y)))
   :value
   (function/lam
    [['L signed] ['eps-left signed] ['x signed]
     ['M signed] ['eps-right signed] ['y signed]
     ['x-close (close 'L 'eps-left 'x)]
     ['y-close (close 'M 'eps-right 'y)]]
    (close-additive 'L 'eps-left 'x
                    (sneg 'M) 'eps-right (sneg 'y)
                    'x-close
                    (close-negate 'M 'eps-right 'y 'y-close)))})

;; s -> L and t -> M give (s - t) -> (L - M): negate the second sequence and
;; reuse the additive limit law.  The modulus is the additive one, unchanged by
;; negation.
(def limit-difference-spec
  {:name 'analysis/limit-difference :universes []
   :type
   (function/forall
    [['s sig-seq] ['t sig-seq] ['L signed] ['M signed]
     ['Ms modulus] ['Mt modulus]
     ['s-converges (converges 's 'L 'Ms)]
     ['t-converges (converges 't 'M 'Mt)]]
    (converges
     (function/lam [['n nat]] (ssub (app 's 'n) (app 't 'n)))
     (ssub 'L 'M)
     (function/lam [['eps signed]]
                   (nadd (app 'Ms 'eps) (app 'Mt signed-zero)))))
   :value
   (function/lam
    [['s sig-seq] ['t sig-seq] ['L signed] ['M signed]
     ['Ms modulus] ['Mt modulus]
     ['s-converges (converges 's 'L 'Ms)]
     ['t-converges (converges 't 'M 'Mt)]]
    (limit-sum 's
               (function/lam [['n nat]] (sneg (app 't 'n)))
               'L (sneg 'M) 'Ms 'Mt
               's-converges
               (limit-negate 't 'M 'Mt 't-converges)))})

(def definition-specs [])
(def theorem-specs [close-subtractive-spec limit-difference-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.limit-arithmetic rainbow.math.rational.signed.limit-negate])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-limit-difference theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.limit-difference))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
