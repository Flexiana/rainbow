(ns rainbow.math.rational.signed.limit-negate
  "Negation preserves signed-rational closeness and limits.

  D63 defines `analysis/close L eps x` as the order band

    L - eps <= x  AND  x <= L + eps.

  Negating reverses signed order.  The two reversed endpoints reduce to the
  corresponding band around `-L`, so the radius and modulus are unchanged.
  Native and axiom-free; builds directly on the D63 convergence module."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convergence :as convergence]))

(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def sig-seq (function/arrow nat signed))
(def modulus (function/arrow signed nat))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sneg [v] (app (function/const* 'signed/negate []) v))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- nat-at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- close [L eps x] (app (function/const* 'analysis/close []) L eps x))
(defn- converges [s L M]
  (app (function/const* 'analysis/converges []) s L M))

(defn- rat-add-comm [a b]
  (app (function/const* 'nnrat/add-commutative []) a b))
(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- conjoin [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- prop-left [a b both]
  (app (function/const* 'proposition/left []) a b both))
(defn- prop-right [a b both]
  (app (function/const* 'proposition/right []) a b both))

;; a <= b implies -b <= -a.  After unfolding signed order, the premise is
;; Pa+Nb <= Pb+Na and the conclusion is Nb+Pa <= Na+Pb; commutativity transports
;; both endpoints through the existing nnrat order-respect law.
(defn- negate-reverses-order [a b ordered]
  (let [Pa (pos a) Na (neg a) Pb (pos b) Nb (neg b)
        old-left (radd Pa Nb)
        new-left (radd Nb Pa)
        old-right (radd Pb Na)
        new-right (radd Na Pb)]
    (rat-at-most-respects
     new-left old-left new-right old-right
     (rat-add-comm Nb Pa) (rat-add-comm Na Pb) ordered)))

(def close-negate-spec
  {:name 'analysis/close-negate :universes []
   :type
   (function/forall
    [['L signed] ['eps signed] ['x signed]
     ['bounded (close 'L 'eps 'x)]]
    (close (sneg 'L) 'eps (sneg 'x)))
   :value
   (function/lam
    [['L signed] ['eps signed] ['x signed]
     ['bounded (close 'L 'eps 'x)]]
    (let [low (ssub 'L 'eps)
          high (sadd 'L 'eps)
          neg-L (sneg 'L)
          neg-x (sneg 'x)
          new-low (ssub neg-L 'eps)
          new-high (sadd neg-L 'eps)
          low<=x (prop-left (sle low 'x) (sle 'x high) 'bounded)
          x<=high (prop-right (sle low 'x) (sle 'x high) 'bounded)
          new-low<=neg-x (negate-reverses-order 'x high x<=high)
          neg-x<=new-high (negate-reverses-order low 'x low<=x)]
      ;; `new-low` reduces to `-(L+eps)` and `new-high` to `-(L-eps)`.
      (conjoin (sle new-low neg-x) (sle neg-x new-high)
               new-low<=neg-x neg-x<=new-high)))})

(def limit-negate-spec
  {:name 'analysis/limit-negate :universes []
   :type
   (function/forall
    [['s sig-seq] ['L signed] ['M modulus]
     ['s-converges (converges 's 'L 'M)]]
    (converges
     (function/lam [['n nat]] (sneg (app 's 'n)))
     (sneg 'L)
     'M))
   :value
   (function/lam
    [['s sig-seq] ['L signed] ['M modulus]
     ['s-converges (converges 's 'L 'M)]]
    (function/lam
     [['eps signed] ['n nat]
      ['large-enough (nat-at-most (app 'M 'eps) 'n)]]
     (app (function/const* 'analysis/close-negate [])
          'L 'eps (app 's 'n)
          (app 's-converges 'eps 'n 'large-enough))))})

(def definition-specs [])
(def theorem-specs [close-negate-spec limit-negate-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      convergence/extend-environment
      (support/extend-with :signed-limit-negate theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
