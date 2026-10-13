(ns rainbow.math.analysis.geometric-threshold
  "The first fully-general-over-n convergence statement for the geometric
  contraction: for the worked start distance d0 = 8 and threshold eps = 1, the
  distance is at most 1 at EVERY step from the modulus 3 onward:

      forall n. (3 <= n)  ->  seq 8 n <= 1.

  This is `convergence/converges-to` specialised to a concrete (d0, eps) with the
  explicit modulus 3 -- no longer a finite list of worked instances but a single
  theorem covering all n past the modulus. The proof unpacks the order witness
  n = 3 + extra (proposition/use-witness on nat/at-most), commutes it to
  extra + 3 (algebra/nat-add-commutative), bounds seq 8 (extra + 3) <= seq 8 3
  by the monotone-convergence bridge (geometric/seq-decreases-with-iteration),
  chains with the worked seq 8 3 <= 1 through nnrat/at-most-transitive, and
  transports the bound back along n = extra + 3 with equality/substitution.

  The remaining generalisation -- arbitrary d0 and eps with a computed modulus --
  needs the archimedean/2^n bound and is tracked separately."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- nat-equality [l r] (function/equality type-level nat l r))
(defn- nat-at-most [l r] (function/app (function/const* 'nat/at-most []) l r))
(defn- nnrat-at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- seq-term [d0 n]
  (function/app (function/const* 'geometric/seq []) d0 n))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- nat-add-commutative [a b]
  (function/app (function/const* 'nat/add-commutative []) a b))
(defn- eq-symmetric [x y h]
  (function/app (function/const* 'equality/symmetric [type-level]) nat x y h))
(defn- eq-transitive [x y z h1 h2]
  (function/app (function/const* 'equality/transitive [type-level])
                nat x y z h1 h2))
(defn- substitute [x y h motive px]
  (function/app (function/const* 'equality/substitution [type-level])
                nat x y h motive px))
(defn- seq-decreases [d0 n k]
  (function/app (function/const* 'geometric/seq-decreases-with-iteration [])
                d0 n k))
(defn- nnrat-at-most-transitive [l m r first second]
  (function/app (function/const* 'nnrat/at-most-transitive [])
                l m r first second))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))
(defn- use-witness [predicate result evidence continue]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nat predicate result evidence continue))

(def start (whole 8))
(def modulus (data-nat 3))

;; forall n. (3 <= n) -> seq 8 n <= 1
(def reaches-one-after-step-3-spec
  {:name 'geometric/reaches-one-after-step-3 :universes []
   :type (function/forall
          [['n nat] ['bound (nat-at-most modulus 'n)]]
          (nnrat-at-most (seq-term start 'n) (whole 1)))
   :value
   (function/lam
    [['n nat] ['bound (nat-at-most modulus 'n)]]
    (let [predicate (function/lam
                     [['extra nat]]
                     (nat-equality (add modulus 'extra) 'n))
          result (nnrat-at-most (seq-term start 'n) (whole 1))
          continue
          (function/lam
           [['extra nat] ['evidence (nat-equality (add modulus 'extra) 'n)]]
           (let [shifted (add 'extra modulus)
                 ;; n = extra + 3  (commute the witness 3 + extra = n)
                 comm (nat-add-commutative modulus 'extra)      ; 3+extra = extra+3
                 n-is-shifted (eq-transitive 'n (add modulus 'extra) shifted
                                             (eq-symmetric (add modulus 'extra)
                                                           'n 'evidence)
                                             comm)              ; n = extra+3
                 ;; seq 8 (extra+3) <= seq 8 3 <= 1
                 bridge (seq-decreases start 'extra modulus)
                 worked (at-most-proof (seq-term start modulus) (whole 1))
                 bound2 (nnrat-at-most-transitive
                         (seq-term start shifted)
                         (seq-term start modulus)
                         (whole 1)
                         bridge worked)]
             ;; transport seq 8 (extra+3) <= 1  to  seq 8 n <= 1
             (substitute shifted 'n
                         (eq-symmetric 'n shifted n-is-shifted)
                         (function/lam [['x nat]]
                                       (nnrat-at-most (seq-term start 'x)
                                                      (whole 1)))
                         bound2)))]
      (use-witness predicate result 'bound continue)))})

(def definition-specs [])
(def theorem-specs [reaches-one-after-step-3-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :geometric-threshold theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.analysis.geometric-threshold))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
