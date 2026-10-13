(ns rainbow.fixtures.nnrat-map-sum-on-independent
  "Finite-sum monotonicity needs bounds only on listed elements.
  Works for empty lists and repeated entries, with no decidable equality."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.list-sum :as sums]))

(def U [:param 'u])
(def D [:succ U])
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(defn- list-of [] (f/app (f/const* 'data/List [D]) 'A))
(defn- nil-of [] (f/app (f/const* 'data/nil [D]) 'A))
(defn- cons-of [] (f/app (f/const* 'data/cons [D]) 'A 'head 'tail))
(defn- member [xs x] (poly 'list/membership 'A xs x))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- sum [mapping xs] (poly 'nnrat/map-sum 'A mapping xs))
(defn- dominated [xs]
  (f/forall [['x 'A] ['in-list (member xs 'x)]]
    (le (f/app 'left 'x) (f/app 'right 'x))))
(defn- result [xs] (le (sum 'left xs) (sum 'right xs)))
(defn- motive [xs] (f/arrow (dominated xs) (result xs)))

(def map-sum-monotone-on-spec
  {:name 'nnrat/map-sum-monotone-on :universes ['u]
   :type (f/forall [['A [:sort D]] ['left (f/arrow 'A nnrat)]
                    ['right (f/arrow 'A nnrat)] ['source (list-of)]]
           (motive 'source))
   :value
   (f/lam [['A [:sort D]] ['left (f/arrow 'A nnrat)]
           ['right (f/arrow 'A nnrat)] ['source (list-of)]]
     (f/app (f/const* 'data/List.rec [D [:zero]]) 'A
       (f/lam [['xs (list-of)]] (motive 'xs))
       (f/lam [['bound (dominated (nil-of))]]
         (app 'nnrat/at-most-reflexive (f/const* 'nnrat/zero [])))
       (f/lam [['head 'A] ['tail (list-of)] ['ih (motive 'tail)]
               ['bound (dominated (cons-of))]]
         (app 'nnrat/add-monotone
           (f/app 'left 'head) (f/app 'right 'head)
           (sum 'left 'tail) (sum 'right 'tail)
           (f/app 'bound 'head
             (app 'proposition/left-disjunct
               (f/equality D 'A 'head 'head) (member 'tail 'head)
               (f/app (f/const* 'equality/reflexive [D]) 'A 'head)))
           (f/app 'ih
             (f/lam [['x 'A] ['in-tail (member 'tail 'x)]]
               (f/app 'bound 'x
                 (app 'proposition/right-disjunct
                   (f/equality D 'A 'x 'head) (member 'tail 'x) 'in-tail))))))
       'source))})
