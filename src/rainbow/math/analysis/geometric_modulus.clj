(ns rainbow.math.analysis.geometric-modulus
  "The geometric-convergence MODULUS -- the last ingredient of the general
  forall-epsilon rational convergence theorem. For a positive accuracy
  eps = make (succ p) q (numerator succ p >= 1, so eps > 0) and start distance
  d0, the contraction distance is at most eps after

      N = numerator(d0) * denominator(eps)

  halving steps:

      seq d0 N  <=  eps.

  Proved native and axiom-free by assembling the finished pieces. Through
  nnrat/at-most-from-cross the goal reduces to the cross inequality
  num(seq d0 N)*den(eps) <= num(eps)*den(seq d0 N); substituting the sequence
  closed form (geometric/seq-numerator-invariant, geometric/seq-denominator) it
  becomes num(d0)*den(eps) <= num(eps)*(den(d0)*2^N); and since the left side is
  exactly N, the chain

      N <= 2^N                                     (nat/at-most-power-two)
        <= den(d0) * 2^N                           (nat/le-multiply-succ, den(d0) succ-headed)
        <= num(eps) * (den(d0) * 2^N)              (nat/le-multiply-succ, num(eps) succ-headed)

  closes it. Combined with geometric/seq-decreases-with-iteration (every later
  iterate is no larger) this yields convergence/converges-to for the geometric
  contraction with the explicit rational/Nat modulus.

  Requires the full analysis stack: geometric/seq(+numerator-invariant),
  geometric/seq-denominator, nat/power, nat/at-most-power-two,
  nat/le-multiply-succ, nnrat/at-most-from-cross, and the equality transport
  lemmas."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))

(defn- mul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- power [b e] (function/app (function/const* 'nat/power []) b e))
(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- den-pred [v]
  (function/app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- make [n dp] (function/app (function/const* 'nnrat/make []) n dp))
(defn- seq-term [d0 n] (function/app (function/const* 'geometric/seq []) d0 n))
(defn- nat-at-most [l r] (function/app (function/const* 'nat/at-most []) l r))
(defn- nnrat-at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))

(defn- at-most-power-two [n]
  (function/app (function/const* 'nat/at-most-power-two []) n))
(defn- le-multiply-succ [f x]
  (function/app (function/const* 'nat/le-multiply-succ []) f x))
(defn- nat-at-most-transitive [l m r first second]
  (function/app (function/const* 'nat/at-most-transitive []) l m r first second))
(defn- numerator-invariant [d0 n]
  (function/app (function/const* 'geometric/seq-numerator-invariant []) d0 n))
(defn- denominator-closed [d0 n]
  (function/app (function/const* 'geometric/seq-denominator []) d0 n))
(defn- at-most-from-cross [l r ordered]
  (function/app (function/const* 'nnrat/at-most-from-cross []) l r ordered))
(defn- congruent [f x y h]
  (function/app (function/const* 'equality/congruent-function
                                 [type-level type-level])
                nat nat f x y h))
(defn- symmetric [x y h]
  (function/app (function/const* 'equality/symmetric [type-level]) nat x y h))
(defn- substitute [x y h motive px]
  (function/app (function/const* 'equality/substitution [type-level])
                nat x y h motive px))

(def two (function/app (function/const* 'data/succ [])
                       (function/app (function/const* 'data/succ [])
                                     (function/const* 'data/zero []))))
(def bool (function/const* 'data/Bool []))
(defn- add [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- nat-equality [x y] (function/equality type-level nat x y))
(defn- eq-transitive [x y z h1 h2]
  (function/app (function/const* 'equality/transitive [type-level])
                nat x y z h1 h2))
(defn- eq-symmetric [x y h]
  (function/app (function/const* 'equality/symmetric [type-level]) nat x y h))
(defn- nat-add-commutative [a b]
  (function/app (function/const* 'nat/add-commutative []) a b))
(defn- seq-decreases [d0 n k]
  (function/app (function/const* 'geometric/seq-decreases-with-iteration [])
                d0 n k))
(defn- reaches-below [d0 p q]
  (function/app (function/const* 'geometric/reaches-below-epsilon []) d0 p q))
(defn- nnrat-at-most-transitive [l m r first second]
  (function/app (function/const* 'nnrat/at-most-transitive []) l m r first second))
(defn- use-witness [predicate result evidence continue]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nat predicate result evidence continue))

;; seq d0 N <= eps  for eps = make (succ p) q and N = num(d0) * den(eps).
(def reaches-below-epsilon-spec
  {:name 'geometric/reaches-below-epsilon :universes []
   :type (function/forall
          [['d0 nnrat] ['p nat] ['q nat]]
          (nnrat-at-most
           (seq-term 'd0 (mul (numerator 'd0)
                              (denominator (make (succ 'p) 'q))))
           (make (succ 'p) 'q)))
   :value
   (function/lam
    [['d0 nnrat] ['p nat] ['q nat]]
    (let [eps (make (succ 'p) 'q)
          nd (numerator 'd0)
          dd (denominator 'd0)
          de (denominator eps)
          ne (numerator eps)
          big-n (mul nd de)
          pn (power two big-n)
          seqn (seq-term 'd0 big-n)
          ddpn (mul dd pn)
          ;; clean : nat-at-most (mul nd de) (mul ne ddpn)
          clean (nat-at-most-transitive
                 big-n pn (mul ne ddpn)
                 (at-most-power-two big-n)
                 (nat-at-most-transitive
                  pn ddpn (mul ne ddpn)
                  (le-multiply-succ (den-pred 'd0) pn)
                  (le-multiply-succ 'p ddpn)))
          ;; e1 : mul (num seqn) de = mul nd de   (numerator invariant)
          e1 (congruent (function/lam [['v nat]] (mul 'v de))
                        (numerator seqn) nd
                        (numerator-invariant 'd0 big-n))
          ;; e2 : mul ne (den seqn) = mul ne ddpn (denominator closed form)
          e2 (congruent (function/lam [['v nat]] (mul ne 'v))
                        (denominator seqn) ddpn
                        (denominator-closed 'd0 big-n))
          ;; transport clean (over A,B) to base-at-most seqn eps (over A',B')
          base1 (substitute big-n (mul (numerator seqn) de)
                            (symmetric (mul (numerator seqn) de) big-n e1)
                            (function/lam [['a nat]]
                                          (nat-at-most 'a (mul ne ddpn)))
                            clean)
          base2 (substitute (mul ne ddpn) (mul ne (denominator seqn))
                            (symmetric (mul ne (denominator seqn))
                                       (mul ne ddpn) e2)
                            (function/lam [['b nat]]
                                          (nat-at-most
                                           (mul (numerator seqn) de) 'b))
                            base1)]
      (at-most-from-cross seqn eps base2)))})

;; General convergence: for every positive eps = make (succ p) q and every step
;; n at least the modulus N = num(d0)*den(eps), the distance is at most eps.
;; This is convergence/converges-to for the geometric contraction, restricted to
;; positive eps (convergence to 0 is impossible for a nonzero sequence). It
;; composes reaches-below-epsilon (the distance is <= eps AT the modulus) with
;; seq-decreases-with-iteration (later iterates are no larger): unpack the order
;; witness n = N + extra, commute to extra + N, bound seq d0 (extra+N) <= seq d0 N
;; <= eps, and transport back along n = extra + N.
(def converges-for-positive-epsilon-spec
  {:name 'geometric/converges-for-positive-epsilon :universes []
   :type (function/forall
          [['d0 nnrat] ['p nat] ['q nat] ['n nat]
           ['bound (nat-at-most
                    (mul (numerator 'd0) (denominator (make (succ 'p) 'q)))
                    'n)]]
          (nnrat-at-most (seq-term 'd0 'n) (make (succ 'p) 'q)))
   :value
   (function/lam
    [['d0 nnrat] ['p nat] ['q nat] ['n nat]
     ['bound (nat-at-most
              (mul (numerator 'd0) (denominator (make (succ 'p) 'q)))
              'n)]]
    (let [eps (make (succ 'p) 'q)
          big-n (mul (numerator 'd0) (denominator eps))
          predicate (function/lam [['extra nat]]
                                  (nat-equality (add big-n 'extra) 'n))
          result (nnrat-at-most (seq-term 'd0 'n) eps)
          continue
          (function/lam
           [['extra nat] ['ev (nat-equality (add big-n 'extra) 'n)]]
           (let [shifted (add 'extra big-n)
                 comm (nat-add-commutative big-n 'extra)
                 n-is-shifted (eq-transitive 'n (add big-n 'extra) shifted
                                             (eq-symmetric (add big-n 'extra)
                                                           'n 'ev)
                                             comm)
                 bridge (seq-decreases 'd0 'extra big-n)
                 reaches (reaches-below 'd0 'p 'q)
                 bound2 (nnrat-at-most-transitive
                         (seq-term 'd0 shifted) (seq-term 'd0 big-n) eps
                         bridge reaches)]
             (substitute shifted 'n
                         (eq-symmetric 'n shifted n-is-shifted)
                         (function/lam [['x nat]]
                                       (nnrat-at-most (seq-term 'd0 'x) eps))
                         bound2)))]
      (use-witness predicate result 'bound continue)))})

(def definition-specs [])
(def theorem-specs
  [reaches-below-epsilon-spec converges-for-positive-epsilon-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :geometric-modulus theorem-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
