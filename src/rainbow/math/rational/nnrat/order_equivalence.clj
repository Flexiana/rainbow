(ns rainbow.math.rational.nnrat.order-equivalence
  "Real-analysis roadmap step 2: the nnrat closure<->base order equivalence.

  nnrat/at-most is the church-encoded reflexive-transitive closure of the cross-product
  order nnrat/base-at-most (base-at-most a b = num a * den b <= num b * den a).  The
  forward direction nnrat/at-most-from-cross (base -> closure) is already in d63.  Here
  we prove the two missing pieces:

    nnrat/base-at-most-transitive : base a x -> base x y -> base a y
    nnrat/at-most-to-cross        : nnrat/at-most a b -> nnrat/base-at-most a b

  base-at-most transitivity is the payoff of step-1 nat multiplicative cancellation:
  scale the two cross-products by the opposite denominators (multiply-right-monotone),
  reorder the degree-3 monomials with the nat-ring tactic, chain, then cancel the shared
  positive factor den_x = succ(dpre x) with nat/at-most-multiply-right-cancel.  The
  reverse closure->base then instantiates the closure recursor at P := (base a _), with
  base-reflexivity for the base case and base-transitivity for the step.

  Together with at-most-from-cross this makes the nnrat order decidable/cancellable at
  the base level -- the gateway to nnrat additive at-most cancellation (step 3) and
  signed order transitivity (step 4).  Native and axiom-free; chains
  rainbow.math.nat.at-most-cancellation (-> nat-ring) on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.nat.at-most-cancellation :as canc]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- base-at-most [p q] (function/app (function/const* 'nnrat/base-at-most []) p q))
(defn- rat-at-most [p q] (function/app (function/const* 'nnrat/at-most []) p q))
(defn- num [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- den [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- dpre [v] (function/app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- nat-transitive [l m r p q]
  (function/app (function/const* 'nat/at-most-transitive []) l m r p q))
(defn- mrm [factor l r ordered]  ; multiply-right-monotone: l<=r -> l*factor <= r*factor
  (function/app (function/const* 'nat/multiply-right-monotone []) factor l r ordered))
(defn- rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left []) left replacement right same ordered))
(defn- rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right []) left right replacement same ordered))
(defn- nat-at-most-reflexive [v]
  (function/app (function/const* 'nat/at-most-reflexive []) v))
(defn- mult-right-cancel [a b f h]
  (function/app (function/const* 'nat/at-most-multiply-right-cancel []) a b f h))
(defn- ring-eq [l r] (:proof (ring/prove-nat-eq l r)))

;; ---- base-at-most transitivity ----------------------------------------------
(def base-transitive-spec
  {:name 'nnrat/base-at-most-transitive :universes []
   :type (function/forall
          [['a nnrat] ['x nnrat] ['y nnrat]
           ['ax (base-at-most 'a 'x)] ['xy (base-at-most 'x 'y)]]
          (base-at-most 'a 'y))
   :value
   (function/lam
    [['a nnrat] ['x nnrat] ['y nnrat]
     ['ax (base-at-most 'a 'x)] ['xy (base-at-most 'x 'y)]]
    (let [na (num 'a) nx (num 'x) ny (num 'y)
          da (den 'a) dx (den 'x) dy (den 'y)
          dpx (dpre 'x)   ; dx = succ dpx (definitionally)
          ;; ax : na*dx <= nx*da ; scale by dy
          s1 (mrm dy (nmul na dx) (nmul nx da) 'ax)          ; (na*dx)*dy <= (nx*da)*dy
          T1 (nmul (nmul na dy) dx)                          ; = (na*dx)*dy reordered
          T2 (nmul (nmul nx dy) da)                          ; = (nx*da)*dy reordered
          T3 (nmul (nmul ny da) dx)                          ; = (ny*dx)*da reordered
          ;; rewrite s1's endpoints to T1 <= T2
          s1a (rewrite-left T1 (nmul (nmul na dx) dy) (nmul (nmul nx da) dy)
                            (ring-eq T1 (nmul (nmul na dx) dy)) s1)   ; T1 <= (nx*da)*dy
          s1' (rewrite-right T1 (nmul (nmul nx da) dy) T2
                             (ring-eq (nmul (nmul nx da) dy) T2) s1a) ; T1 <= T2
          ;; xy : nx*dy <= ny*dx ; scale by da
          s2 (mrm da (nmul nx dy) (nmul ny dx) 'xy)          ; (nx*dy)*da <= (ny*dx)*da
          s2' (rewrite-right T2 (nmul (nmul ny dx) da) T3
                             (ring-eq (nmul (nmul ny dx) da) T3) s2)  ; T2 <= T3
          chained (nat-transitive T1 T2 T3 s1' s2')          ; T1 <= T3  i.e. (na*dy)*dx <= (ny*da)*dx
          ]
      ;; cancel the shared positive factor dx = succ dpx
      (mult-right-cancel (nmul na dy) (nmul ny da) dpx chained)))})

;; ---- closure -> base --------------------------------------------------------
(def at-most-to-cross-spec
  {:name 'nnrat/at-most-to-cross :universes []
   :type (function/forall
          [['a nnrat] ['b nnrat] ['h (rat-at-most 'a 'b)]]
          (base-at-most 'a 'b))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['h (rat-at-most 'a 'b)]]
    (function/app
     'h
     ;; P := \x. base-at-most a x
     (function/lam [['x nnrat]] (base-at-most 'a 'x))
     ;; step : \before after (o: base before after)(pb: base a before). base a after
     (function/lam [['before nnrat] ['after nnrat]
                    ['o (base-at-most 'before 'after)]
                    ['pb (base-at-most 'a 'before)]]
                   (function/app (function/const* 'nnrat/base-at-most-transitive [])
                                 'a 'before 'after 'pb 'o))
     ;; base : P a = base a a  (reflexive cross product)
     (nat-at-most-reflexive (nmul (num 'a) (den 'a)))))})

(def definition-specs [])
(def theorem-specs [base-transitive-spec at-most-to-cross-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      canc/extend-environment
      (support/extend-with :nnrat-order-equivalence
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
