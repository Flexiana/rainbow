(ns rainbow.math.rational.nnrat.archimedean
  "The Archimedean reciprocal limit helper for nonnegative rationals.

  If x <= y + 1/(k+1) for every natural k, then x <= y.  At the cross-product
  level, choose k = den(y)*den(x).  If A = num(x)*den(y), B = num(y)*den(x),
  K = den(y)*den(x), and M = succ K, the chosen hypothesis normalizes to

      M*A <= M*B + K.

  Decidability of A <= B closes the positive branch.  In the negative branch,
  B <= A has a witness B+d=A.  The zero case is equality; a successor witness
  forces M <= K, i.e. succ K <= K, contradicting nat/not-equal-successor-add.

  Native and axiom-free; chains nnrat-order-equivalence, nat at-most
  cancellation, and the nat-ring proof-term generator on the D63 checkpoint."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.rational.nnrat.order-equivalence :as oe]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero-nat (function/const* 'data/zero []))
(def one-nat (function/app (function/const* 'data/succ []) zero-nat))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- make [n dp] (function/app (function/const* 'nnrat/make []) n dp))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- num [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- den [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- dpre [v] (function/app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- combine [l r]
  (function/app (function/const* 'nnrat/combine-denominator-predecessors []) l r))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- eq-bool [a b] (function/equality type-level bool a b))

(defn- from-cross [a b h]
  (function/app (function/const* 'nnrat/at-most-from-cross []) a b h))
(defn- to-cross [a b h]
  (function/app (function/const* 'nnrat/at-most-to-cross []) a b h))
(defn- combine-law [l r]
  (function/app (function/const* 'nnrat/denominator-combine []) l r))
(defn- decide-at-most [a b]
  (function/app (function/const* 'nat/decide-at-most []) a b))
(defn- decide-true-sound [a b h]
  (function/app (function/const* 'nat/decide-at-most-true-sound []) a b h))
(defn- decide-false-reverse [a b h]
  (function/app (function/const* 'nat/decide-at-most-false-reverse []) a b h))
(defn- bool-rec [motive false-case true-case choice]
  (function/app (function/const* 'data/Bool.rec [[:zero]])
                motive false-case true-case choice))
(defn- nat-rec [motive base step value]
  (function/app (function/const* 'data/Nat.rec [[:zero]]) motive base step value))
(defn- reflexive-nat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- reflexive-bool [v]
  (function/app (function/const* 'equality/reflexive [type-level]) bool v))
(defn- symmetric [l r p]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r p))
(defn- transitive [l m r p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- congruent [mapping l r p]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r p))
(defn- rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left [])
                left replacement right same ordered))
(defn- rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right [])
                left right replacement same ordered))
(defn- nat-transitive [l m r p q]
  (function/app (function/const* 'nat/at-most-transitive []) l m r p q))
(defn- nat-reflexive [v]
  (function/app (function/const* 'nat/at-most-reflexive []) v))
(defn- add-left-cancel [a b prefix h]
  (function/app (function/const* 'nat/at-most-add-left-cancel []) a b prefix h))
(defn- multiply-successor-right [v predecessor]
  (function/app (function/const* 'nat/multiply-successor-right []) v predecessor))
(defn- multiply-commutative [a b]
  (function/app (function/const* 'nat/multiply-commutative []) a b))
(defn- multiply-one-right [v]
  (function/app (function/const* 'nat/multiply-one-right []) v))
(defn- add-zero-right [v]
  (function/app (function/const* 'algebra/nat-add-zero-right []) v))
(defn- witness [predicate value proof]
  (function/app (function/const* 'proposition/witness [type-level])
                nat predicate value proof))
(defn- use-witness [predicate goal exists handler]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nat predicate goal exists handler))
(defn- not-equal-successor-add [v extra same]
  (function/app (function/const* 'nat/not-equal-successor-add []) v extra same))
(defn- explode [goal falsity]
  (function/app (function/const* 'proposition/explode []) goal falsity))
(defn- ring-eq [l r] (:proof (ring/prove-nat-eq l r)))

(def at-most-of-all-plus-reciprocal-spec
  {:name 'nnrat/at-most-of-all-plus-reciprocal
   :universes []
   :type
   (function/forall
    [['x nnrat] ['y nnrat]
     ['bounded
      (function/forall
       [['k nat]]
       (rat-at-most 'x (radd 'y (make one-nat 'k))))]]
    (rat-at-most 'x 'y))
   :value
   (function/lam
    [['x nnrat] ['y nnrat]
     ['bounded
      (function/forall
       [['k nat]]
       (rat-at-most 'x (radd 'y (make one-nat 'k))))]]
    (let [nx (num 'x) ny (num 'y)
          dxp (dpre 'x) dyp (dpre 'y)
          dx (succ dxp) dy (succ dyp)
          A (nmul nx dy)
          B (nmul ny dx)
          K (nmul dy dx)
          M (succ K)
          epsilon (make one-nat K)
          sum (radd 'y epsilon)
          packed-sum-den (succ (combine dyp K))
          raw-sum-num (nadd (nmul ny M) (nmul one-nat dy))
          transported-left (nmul nx (nmul dy M))
          raw-right (nmul raw-sum-num dx)
          canonical-left (nmul M A)
          canonical-right-with-one
          (nadd (nmul M B) (nmul (nmul one-nat dy) dx))
          canonical-right (nadd (nmul M B) K)
          ;; Instantiate the universal bound at K = den(y)*den(x).
          chosen (function/app 'bounded K)
          cross (to-cross 'x sum chosen)
          ;; Transport the packed denominator of y+epsilon to dy*M.
          den-eq (combine-law dyp K)
          den-cong (congruent (function/lam [['v nat]] (nmul nx 'v))
                              packed-sum-den (nmul dy M) den-eq)
          h1 (rewrite-left transported-left (nmul nx packed-sum-den) raw-right
                           (symmetric (nmul nx packed-sum-den) transported-left den-cong)
                           cross)
          ;; Normalize both cross-products to M*A <= M*B + K.
          h2 (rewrite-left canonical-left transported-left raw-right
                           (ring-eq canonical-left transported-left) h1)
          h3 (rewrite-right canonical-left raw-right canonical-right-with-one
                            (ring-eq raw-right canonical-right-with-one) h2)
          one-dy (transitive (nmul one-nat dy) (nmul dy one-nat) dy
                             (multiply-commutative one-nat dy)
                             (multiply-one-right dy))
          one-k (congruent (function/lam [['v nat]] (nmul 'v dx))
                           (nmul one-nat dy) dy one-dy)
          right-eq (congruent (function/lam [['v nat]] (nadd (nmul M B) 'v))
                              (nmul (nmul one-nat dy) dx) K one-k)
          normalized (rewrite-right canonical-left canonical-right-with-one
                                    canonical-right right-eq h3)
          decision (decide-at-most A B)
          goal (rat-at-most 'x 'y)
          motive (function/lam [['choice bool]]
                               (function/arrow (eq-bool decision 'choice) goal))
          true-case
          (function/lam
           [['is-true (eq-bool decision true-value)]]
           (from-cross 'x 'y (decide-true-sound A B 'is-true)))
          false-case
          (function/lam
           [['is-false (eq-bool decision false-value)]]
           (use-witness
            (function/lam [['d nat]] (eq-nat (nadd B 'd) A))
            goal
            (decide-false-reverse A B 'is-false)
            (function/lam
             [['d nat] ['bd-eq-a (eq-nat (nadd B 'd) A)]]
             (function/app
              (nat-rec
               (function/lam
                [['dv nat]]
                (function/arrow (eq-nat (nadd B 'dv) A) goal))
               ;; d=0: A=B, hence x<=y by cross-product reflexivity and transport.
               (function/lam
                [['b0-eq-a (eq-nat (nadd B zero-nat) A)]]
                (let [a-eq-b0 (symmetric (nadd B zero-nat) A 'b0-eq-a)
                      a-eq-b (transitive A (nadd B zero-nat) B
                                         a-eq-b0 (add-zero-right B))]
                  (from-cross 'x 'y
                              (rewrite-right A A B a-eq-b (nat-reflexive A)))))
               ;; d=succ d': substituting A=B+succ d' in the normalized bound
               ;; yields M*(succ d')<=K, while M<=M*(succ d'); thus succ K<=K.
               (function/lam
                [['dp nat]
                 ['ignored
                  (function/arrow (eq-nat (nadd B 'dp) A) goal)]]
                (function/lam
                 [['bsd-eq-a (eq-nat (nadd B (succ 'dp)) A)]]
                 (let [Msd (nmul M (succ 'dp))
                       MB (nmul M B)
                       expanded-left (nadd MB Msd)
                       scaled-eq
                       (congruent (function/lam [['v nat]] (nmul M 'v))
                                  (nadd B (succ 'dp)) A 'bsd-eq-a)
                       expanded-eq
                       (transitive expanded-left (nmul M (nadd B (succ 'dp)))
                                   canonical-left
                                   (ring-eq expanded-left
                                            (nmul M (nadd B (succ 'dp))))
                                   scaled-eq)
                       substituted
                       (rewrite-left expanded-left canonical-left canonical-right
                                     expanded-eq normalized)
                       msd-le-k (add-left-cancel Msd K MB substituted)
                       msd-expanded (nadd M (nmul M 'dp))
                       m-le-expanded
                       (witness (function/lam [['e nat]]
                                             (eq-nat (nadd M 'e) msd-expanded))
                                (nmul M 'dp) (reflexive-nat msd-expanded))
                       m-le-msd
                       (rewrite-right M msd-expanded Msd
                                      (symmetric Msd msd-expanded
                                                 (multiply-successor-right M 'dp))
                                      m-le-expanded)
                       descending (nat-transitive M Msd K m-le-msd msd-le-k)]
                   (explode
                    goal
                    (use-witness
                     (function/lam [['e nat]]
                                   (eq-nat (nadd (succ K) 'e) K))
                     (function/const* 'proposition/falsity [])
                     descending
                     (function/lam
                      [['e nat] ['too-large (eq-nat (nadd (succ K) 'e) K)]]
                      (not-equal-successor-add
                       K 'e (symmetric (nadd (succ K) 'e) K 'too-large))))))))
               'd)
              'bd-eq-a))))]
      (function/app (bool-rec motive false-case true-case decision)
                    (reflexive-bool decision))))})

(def definition-specs [])
(def theorem-specs [at-most-of-all-plus-reciprocal-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      oe/extend-environment
      (support/extend-with :nnrat-archimedean theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
