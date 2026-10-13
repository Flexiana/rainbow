(ns rainbow.math.rational.signed.no-zero-divisors
  "No-zero-divisors sub-foundation for strict convexity: nonzero facts and (building up)
  a != 0 -> b != 0 -> a*b != 0. Brick 1 first: 1 !~ 0."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.infinite :as nat-infinite]
            [rainbow.math.rational.nnrat.identities :as nnrat-identities]
            [rainbow.math.rational.signed.strict-order :as strict-order]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence-laws]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- app [f & a] (apply function/app f a))
(defn- nnrat-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(def ^:private nnrat-one (function/const* 'nnrat/one []))
(def ^:private nnrat-zero (function/const* 'nnrat/zero []))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))
(defn- zero-not-succ [v] (app (function/const* 'nat/zero-not-successor []) v))
(defn- eq-symm [lvl A x y h] (function/app (function/const* 'equality/symmetric [lvl]) A x y h))

(def one-not-equivalent-zero-spec
  {:name 'nnrat/one-not-equivalent-zero
   :universes []
   :type (pneg (nnrat-equiv nnrat-one nnrat-zero))
   :value (function/lam
           [['h (nnrat-equiv nnrat-one nnrat-zero)]]
           ;; h : equality Nat (succ zero) zero (by defeq); flip and discriminate
           (app (zero-not-succ nat-zero)
                (eq-symm [:succ [:zero]] nat (succ nat-zero) nat-zero 'h)))})

;; --- brick 2: signed 1 !~ 0 (lift brick 1 through the stuck add-x-zero) ---
(def ^:private sone (function/const* 'signed/one []))
(def ^:private szero (function/const* 'signed/zero []))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- nnrat-add [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-trans [a b c h1 h2] (app (function/const* 'nnrat/equivalent-transitive []) a b c h1 h2))
(defn- nn-sym [a b h] (app (function/const* 'nnrat/equivalent-symmetric []) a b h))
(defn- add-zero-right [q] (app (function/const* 'nnrat/add-zero-right []) q))
(defn- one-not-zero-nnrat [] (function/const* 'nnrat/one-not-equivalent-zero []))

(def signed-one-not-equivalent-zero-spec
  {:name 'signed/one-not-equivalent-zero
   :universes []
   :type (pneg (seqv sone szero))
   :value (function/lam
           [['h (seqv sone szero)]]
           ;; h :defeq nnrat-equivalent (add one zero)(add zero zero); transport to one~zero,
           ;; then discharge via brick 1.
           (let [A (nnrat-add nnrat-one nnrat-zero)
                 B (nnrat-add nnrat-zero nnrat-zero)]
             (app (one-not-zero-nnrat)
                  (nn-trans nnrat-one A nnrat-zero
                            (nn-sym A nnrat-one (add-zero-right nnrat-one))   ; one ~ A
                            (nn-trans A B nnrat-zero 'h (add-zero-right nnrat-zero))))))})

;; --- brick 3: 0 < 1 (first strict inequality) ---
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- slt [a b] (app (function/const* 'signed/less-than []) a b))
(defn- s-eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- lt-intro [x y le neq] (app (function/const* 'signed/less-than-intro []) x y le neq))
(defn- zle-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- zero-at-most-nnrat [q] (app (function/const* 'nnrat/zero-at-most []) q))

(def zero-less-than-one-spec
  {:name 'signed/zero-less-than-one
   :universes []
   :type (slt szero sone)
   :value (lt-intro szero sone
                    (zle-nn sone (zero-at-most-nnrat nnrat-one))            ; 0 <= 1
                    (function/lam [['h (seqv szero sone)]]                  ; not (0 ~ 1)
                                  (app (function/const* 'signed/one-not-equivalent-zero [])
                                       (s-eqv-sym szero sone 'h))))})       ; 1 ~ 0 -> falsity

(def theorem-specs [one-not-equivalent-zero-spec signed-one-not-equivalent-zero-spec
                    zero-less-than-one-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      nat-infinite/extend-environment
      nnrat-identities/extend-environment
      strict-order/extend-environment
      multiply-order/extend-environment
      equivalence-laws/extend-environment
      farkas/extend-environment
      (support/extend-with :signed-no-zero-divisors theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
