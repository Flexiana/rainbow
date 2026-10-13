(ns rainbow.math.rational.nnrat.null-sequence
  "Real-analysis toward the OR payoff: null (converging-to-zero) sequences of nonnegative
  rationals, and the COMPARISON TEST -- a sequence dominated by a null sequence is null.

    analysis/null s M      := forall eps n, M eps <= n -> s n <= eps
    analysis/null-dominated : (forall n, t n <= s n) -> null s M -> null t M

  Because nnrat values are >= 0, convergence to zero is one-sided (an upper bound that
  shrinks below every eps), so this needs NO signed arithmetic -- only nnrat order
  transitivity.  This is the exact instrument behind contraction/value-iteration
  convergence: if the error e(n) <= gamma^n * C and gamma^n -> 0, then e -> 0.

  Native and axiom-free; chains rainbow.math.rational.nnrat.minmax on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.minmax :as minmax]))

(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-seq (function/arrow nat nnrat))
(def nnrat-modulus (function/arrow nnrat nat))

(defn- app [f & args] (apply function/app f args))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- rat-transitive [l m r p q]
  (function/app (function/const* 'nnrat/at-most-transitive []) l m r p q))
(defn- the-null [s M] (function/app (function/const* 'analysis/null []) s M))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- at-most-max [x y hi xh yh]
  (function/app (function/const* 'minmax/at-most-max []) x y hi xh yh))

;; s converges to 0 (from above): for n past the modulus, s n <= eps
(def null-spec
  {:name 'analysis/null :kind :definition :universes []
   :type (function/arrow nnrat-seq nnrat-modulus 'Prop)
   :value (function/lam [['s nnrat-seq] ['M nnrat-modulus]]
                        (function/forall
                         [['eps nnrat] ['n nat]]
                         (function/arrow (nat-at-most (app 'M 'eps) 'n)
                                         (rat-at-most (app 's 'n) 'eps))))})

;; comparison test: t dominated by a null s (with the same modulus) is null
(def null-dominated-spec
  {:name 'analysis/null-dominated :universes []
   :type (function/forall
          [['s nnrat-seq] ['t nnrat-seq] ['M nnrat-modulus]
           ['dom (function/forall [['n nat]] (rat-at-most (app 't 'n) (app 's 'n)))]
           ['hs (the-null 's 'M)]]
          (the-null 't 'M))
   :value
   (function/lam
    [['s nnrat-seq] ['t nnrat-seq] ['M nnrat-modulus]
     ['dom (function/forall [['n nat]] (rat-at-most (app 't 'n) (app 's 'n)))]
     ['hs (the-null 's 'M)]]
    (function/lam
     [['eps nnrat] ['n nat] ['hn (nat-at-most (app 'M 'eps) 'n)]]
     ;; t n <= s n <= eps
     (rat-transitive (app 't 'n) (app 's 'n) 'eps
                     (app 'dom 'n)
                     (app 'hs 'eps 'n 'hn))))})

;; null sequences are closed under pointwise max (common modulus)
(def null-max-spec
  {:name 'analysis/null-max :universes []
   :type (function/forall
          [['s nnrat-seq] ['t nnrat-seq] ['M nnrat-modulus]
           ['hs (the-null 's 'M)] ['ht (the-null 't 'M)]]
          (the-null (function/lam [['n nat]] (rmax (app 's 'n) (app 't 'n))) 'M))
   :value
   (function/lam
    [['s nnrat-seq] ['t nnrat-seq] ['M nnrat-modulus]
     ['hs (the-null 's 'M)] ['ht (the-null 't 'M)]]
    (function/lam
     [['eps nnrat] ['n nat] ['hn (nat-at-most (app 'M 'eps) 'n)]]
     ;; max (s n) (t n) <= eps  from  s n <= eps  and  t n <= eps
     (at-most-max (app 's 'n) (app 't 'n) 'eps
                  (app 'hs 'eps 'n 'hn)
                  (app 'ht 'eps 'n 'hn))))})

(def definition-specs [null-spec])
(def theorem-specs [null-dominated-spec null-max-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      minmax/extend-environment
      (support/extend-with :nnrat-null-sequence
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
