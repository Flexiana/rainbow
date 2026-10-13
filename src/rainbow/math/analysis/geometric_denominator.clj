(ns rainbow.math.analysis.geometric-denominator
  "The denominator half of the geometric-sequence closed form:

      denominator (seq d0 N) = denominator d0 * 2^N     for every N,

  completing (with geometric/seq-numerator-invariant) the closed form
  seq d0 N = num(d0) / (den(d0) * 2^N) that the convergence modulus needs. Proved
  axiom-free by induction on N. The base uses nat/multiply-one-right (2^0 = 1).
  The step uses that halving doubles the denominator -- denominator (seq d0 (succ
  N)) reduces to D + (D + 0) where D = denominator (seq d0 N) -- and that
  2^(N+1) = 2 * 2^N reduces to P + (P + 0) where P = 2^N; substituting the
  induction hypothesis D = den(d0) * P and expanding den(d0) * (P + (P + 0)) with
  the freshly proved nat/multiply-distributes-add and nat/multiply-zero-right
  makes both sides equal.

  Requires geometric/seq, nnrat/denominator, nat/power, nat/multiply,
  nat/multiply-distributes-add, nat/multiply-zero-right, nat/multiply-one-right
  (d63 + nat-add-order + half-monotone + geometric-sequence + nat-power +
  nat-distributive)."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero-t (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))

(defn- mul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- add [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- power [b e] (function/app (function/const* 'nat/power []) b e))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- seq-term [d0 n] (function/app (function/const* 'geometric/seq []) d0 n))
(defn- eq [x y] (function/equality type-level nat x y))
(defn- trans [x y z h1 h2]
  (function/app (function/const* 'equality/transitive [type-level])
                nat x y z h1 h2))
(defn- sym [x y h]
  (function/app (function/const* 'equality/symmetric [type-level]) nat x y h))
(defn- cong [f x y h]
  (function/app (function/const* 'equality/congruent-function
                                 [type-level type-level])
                nat nat f x y h))
(defn- distributes [a b c]
  (function/app (function/const* 'nat/multiply-distributes-add []) a b c))
(defn- multiply-zero-right [x]
  (function/app (function/const* 'nat/multiply-zero-right []) x))
(defn- multiply-one-right [x]
  (function/app (function/const* 'nat/multiply-one-right []) x))

(def two (function/app (function/const* 'data/succ [])
                       (function/app (function/const* 'data/succ []) zero-t)))

;; denominator (seq d0 N) = denominator d0 * 2^N
(def seq-denominator-spec
  {:name 'geometric/seq-denominator :universes []
   :type (function/forall
          [['d0 nnrat] ['n nat]]
          (eq (denominator (seq-term 'd0 'n))
              (mul (denominator 'd0) (power two 'n))))
   :value
   (function/lam
    [['d0 nnrat] ['n nat]]
    (let [dd (denominator 'd0)
          motive (function/lam
                  [['m nat]]
                  (eq (denominator (seq-term 'd0 'm))
                      (mul dd (power two 'm))))
          ;; base: den(seq d0 0) = dd, dd * 2^0 = dd * 1; symmetric multiply-one-right.
          base (sym (mul dd (function/app (function/const* 'data/succ []) zero-t))
                    dd
                    (multiply-one-right dd))
          step
          (function/lam
           [['k nat] ['ih (function/app motive 'k)]]
           (let [d (denominator (seq-term 'd0 'k))     ; D
                 p (power two 'k)                       ; P
                 mp (mul dd p)                          ; den(d0) * P
                 ;; RHS = den(d0) * (P + (P + 0)) decomposed:
                 dist1 (distributes dd p (add p zero-t))
                 dist2 (distributes dd p zero-t)
                 zr (multiply-zero-right dd)
                 dd-p-zero (trans (mul dd (add p zero-t))
                                  (add mp (mul dd zero-t))
                                  (add mp zero-t)
                                  dist2
                                  (cong (function/lam [['v nat]] (add mp 'v))
                                        (mul dd zero-t) zero-t zr))
                 rhs-eq (trans (mul dd (add p (add p zero-t)))
                               (add mp (mul dd (add p zero-t)))
                               (add mp (add mp zero-t))
                               dist1
                               (cong (function/lam [['v nat]] (add mp 'v))
                                     (mul dd (add p zero-t))
                                     (add mp zero-t)
                                     dd-p-zero))
                 ;; LHS = D + (D + 0), substitute ih (D = mp) in both places.
                 e-lhs1 (cong (function/lam [['v nat]] (add 'v (add d zero-t)))
                              d mp 'ih)
                 e-lhs2 (cong (function/lam [['v nat]] (add mp (add 'v zero-t)))
                              d mp 'ih)
                 lhs-eq (trans (add d (add d zero-t))
                               (add mp (add d zero-t))
                               (add mp (add mp zero-t))
                               e-lhs1 e-lhs2)]
             (trans (add d (add d zero-t))
                    (add mp (add mp zero-t))
                    (mul dd (add p (add p zero-t)))
                    lhs-eq
                    (sym (mul dd (add p (add p zero-t)))
                         (add mp (add mp zero-t))
                         rhs-eq))))]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive base step 'n)))})

(def definition-specs [])
(def theorem-specs [seq-denominator-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :geometric-denominator theorem-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
