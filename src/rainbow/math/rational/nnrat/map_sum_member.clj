(ns rainbow.math.rational.nnrat.map-sum-member
  "A listed nonnegative rational term is bounded by its finite sum.
  Constructive membership induction; no decidable equality, normalization,
  or duplicate-freedom premise. Kernel-checked and axiom-free on D63."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.metric-separation :as metric]))

(def U [:param 'u])
(def data-u [:succ U])
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(def zero (f/const* 'nnrat/zero []))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(defn- list-of [A] (f/app (f/const* 'data/List [data-u]) A))
(defn- nil-of [A] (f/app (f/const* 'data/nil [data-u]) A))
(defn- cons-of [A x xs] (f/app (f/const* 'data/cons [data-u]) A x xs))
(defn- member [xs x] (poly 'list/membership 'A xs x))
(defn- sum [xs] (poly 'nnrat/map-sum 'A 'mapping xs))
(defn- add [a b] (app 'nnrat/add a b))
(defn- le [a b] (app 'nnrat/at-most a b))

(defn- below-add-right [a b]
  (app 'nnrat/at-most-transitive a (add a zero) (add a b)
    (app 'nnrat/equivalent-to-at-most a (add a zero)
      (app 'nnrat/equivalent-symmetric (add a zero) a
        (app 'nnrat/add-zero-right a)))
    (app 'nnrat/add-monotone a a zero b
      (app 'nnrat/at-most-reflexive a) (app 'nnrat/zero-at-most b))))

(def map-sum-at-least-member-spec
  (let [base [['A [:sort data-u]] ['mapping (f/arrow 'A nnrat)]]
        selected (fn [xs] [['selected 'A] ['member (member xs 'selected)]])
        result (fn [xs] (le (f/app 'mapping 'selected) (sum xs)))
        motive (f/lam [['items (list-of 'A)]]
                 (f/forall (selected 'items) (result 'items)))
        bindings (into base (into [['items (list-of 'A)]] (selected 'items)))]
    {:name 'nnrat/map-sum-at-least-member :universes ['u]
     :type (f/forall bindings (result 'items))
     :value
     (f/lam bindings
       (f/app (f/const* 'data/List.rec [data-u [:zero]]) 'A motive
         (f/lam (selected (nil-of 'A))
           (app 'proposition/explode (result (nil-of 'A)) 'member))
         (f/lam
           (into [['head 'A] ['tail (list-of 'A)] ['ih (f/app motive 'tail)]]
                 (selected (cons-of 'A 'head 'tail)))
           (let [a (f/app 'mapping 'head) b (sum 'tail) total (add a b)
                 same (f/equality data-u 'A 'selected 'head)
                 tail-member (member 'tail 'selected)]
             (app 'proposition/use-disjunction same tail-member
               (le (f/app 'mapping 'selected) total) 'member
               (f/lam [['same same]]
                 (f/app (f/const* 'equality/reverse-substitution [data-u])
                   'A 'selected 'head 'same
                   (f/lam [['candidate 'A]] (le (f/app 'mapping 'candidate) total))
                   (below-add-right a b)))
               (f/lam [['in-tail tail-member]]
                 (app 'nnrat/at-most-transitive (f/app 'mapping 'selected) b total
                   (f/app 'ih 'selected 'in-tail)
                   (app 'nnrat/at-most-respects-equivalence b b total (add b a)
                     (app 'nnrat/equivalent-reflexive b)
                     (app 'nnrat/add-commutative a b)
                     (below-add-right b a)))))))
         'items 'selected 'member))}))

(def theorem-specs [map-sum-at-least-member-spec])
(defn extend-environment [env]
  (-> env metric/extend-environment
      (support/extend-with :nnrat-map-sum-member theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
