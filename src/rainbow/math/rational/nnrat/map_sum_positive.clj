(ns rainbow.math.rational.nnrat.map-sum-positive
  "Strict positivity of finite exact nonnegative-rational sums.

  If a listed element maps to a positive rational, the full finite map-sum is
  positive.  The proof is constructive List.rec induction over membership and
  needs neither decidable equality nor duplicate freedom.  This is the generic
  path-term-to-positive-transition bridge for finite Markov composition.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.list-sum :as list-sum]
            [rainbow.math.rational.nnrat.positive :as positive]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- list-of [element]
  (app (function/const* 'data/List [data-u]) element))
(defn- nil-list [element]
  (app (function/const* 'data/nil [data-u]) element))
(defn- cons-list [element head tail]
  (app (function/const* 'data/cons [data-u]) element head tail))
(defn- membership [element items value]
  (app (function/const* 'list/membership [U]) element items value))
(defn- map-sum [element mapping items]
  (app (function/const* 'nnrat/map-sum [U]) element mapping items))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- positive-rational [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- eq-state [element left right]
  (function/equality data-u element left right))
(defn- substitute-state [element left right same predicate at-left]
  (app (function/const* 'equality/substitution [data-u])
       element left right same predicate at-left))
(defn- use-disjunction [left right result evidence on-left on-right]
  (app (function/const* 'proposition/use-disjunction [])
       left right result evidence on-left on-right))
(defn- explode [result contradiction]
  (app (function/const* 'proposition/explode []) result contradiction))

(def map-sum-positive-of-member-spec
  (let [motive
        (function/lam
         [['items (list-of 'A)]]
         (function/forall
          [['selected 'A]
           ['member (membership 'A 'items 'selected)]
           ['selected-positive
            (positive-rational (app 'mapping 'selected))]]
          (positive-rational (map-sum 'A 'mapping 'items))))]
    {:name 'nnrat/map-sum-positive-of-member
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['mapping (function/arrow 'A nnrat)]
       ['items (list-of 'A)]
       ['selected 'A]
       ['member (membership 'A 'items 'selected)]
       ['selected-positive
        (positive-rational (app 'mapping 'selected))]]
      (positive-rational (map-sum 'A 'mapping 'items)))
     :value
     (function/lam
      [['A type-u]
       ['mapping (function/arrow 'A nnrat)]
       ['items (list-of 'A)]
       ['selected 'A]
       ['member (membership 'A 'items 'selected)]
       ['selected-positive
        (positive-rational (app 'mapping 'selected))]]
      (app
       (function/const* 'data/List.rec [data-u zero-level])
       'A motive
       (function/lam
        [['selected 'A]
         ['impossible-member (membership 'A (nil-list 'A) 'selected)]
         ['ignored-positive
          (positive-rational (app 'mapping 'selected))]]
        (explode
         (positive-rational (map-sum 'A 'mapping (nil-list 'A)))
         'impossible-member))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (app motive 'tail)]
         ['selected 'A]
         ['member
          (membership
           'A (cons-list 'A 'head 'tail) 'selected)]
         ['selected-positive
          (positive-rational (app 'mapping 'selected))]]
        (let [same (eq-state 'A 'selected 'head)
              tail-member (membership 'A 'tail 'selected)
              head-value (app 'mapping 'head)
              tail-total (map-sum 'A 'mapping 'tail)
              total (radd head-value tail-total)]
          (use-disjunction
           same tail-member (positive-rational total) 'member
           (function/lam
            [['selected-is-head same]]
            (let [head-positive
                  (substitute-state
                   'A 'selected 'head 'selected-is-head
                   (function/lam
                    [['candidate 'A]]
                    (positive-rational (app 'mapping 'candidate)))
                   'selected-positive)]
              (app
               (function/const* 'nnrat/add-positive-left [])
               head-value tail-total head-positive)))
           (function/lam
            [['selected-in-tail tail-member]]
            (let [tail-positive
                  (app 'induction-hypothesis
                       'selected 'selected-in-tail 'selected-positive)]
              (app
               (function/const* 'nnrat/add-positive-right [])
               head-value tail-total tail-positive))))))
       'items 'selected 'member 'selected-positive))}))

(def definition-specs [])
(def theorem-specs [map-sum-positive-of-member-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.list-sum rainbow.math.rational.nnrat.positive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :nnrat-map-sum-positive theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.map-sum-positive))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
