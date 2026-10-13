(ns rainbow.fixtures.nnrat-sum-distance-induction
  "Independent proof from 14a7a53, retained as test evidence only."
  (:require [rainbow.math.logic.function :as function]))
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(defn- app [f & xs] (apply function/app f xs))
(defn- call [n & xs] (apply app (function/const* n []) xs))
(defn- list-of [A] (app (function/const* 'data/List [data-u]) A))
(defn- map-sum [A f xs] (app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- rle [a b] (call 'nnrat/at-most a b))
(defn- radd [a b] (call 'nnrat/add a b))
(defn- scalar-distance [a b] (call 'nnrat/distance a b))
(defn- equivalent-reflexive [a] (call 'nnrat/equivalent-reflexive a))
(defn- order-transitive [a b c h k] (call 'nnrat/at-most-transitive a b c h k))
(defn- add-left-monotone [a b c h] (call 'nnrat/add-left-monotone a b c h))

(def map-sum-distance-bound-spec
  "The finite triangle inequality for map-sum: the distance between two
  finite sums is at most the finite sum of pointwise distances. List
  induction; each cons step is the scalar subadditivity above followed by
  left-monotone addition of the induction hypothesis. This is the
  NNRAT-valued bridge the Dobrushin residual expansion asked for: the
  kernel-step total variation is a distance between map-sums, and this
  theorem opens it into a sum of per-source distances."
  {:name 'test/nnrat-map-sum-distance-bound-by-induction
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['f (function/arrow 'A nnrat)]
     ['g (function/arrow 'A nnrat)]
     ['items (list-of 'A)]]
    (rle (scalar-distance (map-sum 'A 'f 'items) (map-sum 'A 'g 'items))
         (map-sum 'A
                  (function/lam
                   [['i 'A]]
                   (scalar-distance (app 'f 'i) (app 'g 'i)))
                  'items)))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)]
     ['g (function/arrow 'A nnrat)]
     ['items (list-of 'A)]]
    (let [pointwise
          (function/lam
           [['i 'A]]
           (scalar-distance (app 'f 'i) (app 'g 'i)))]
      (app
       (function/const* 'data/List.rec [data-u [:zero]])
       'A
       (function/lam
        [['ys (list-of 'A)]]
        (rle (scalar-distance (map-sum 'A 'f 'ys) (map-sum 'A 'g 'ys))
             (map-sum 'A pointwise 'ys)))
       (app (function/const* 'nnrat/distance-at-most-zero-of-equivalent [])
            nnrat-zero nnrat-zero (equivalent-reflexive nnrat-zero))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['ih (rle (scalar-distance (map-sum 'A 'f 'tail)
                                    (map-sum 'A 'g 'tail))
                   (map-sum 'A pointwise 'tail))]]
        (let [head-distance
              (scalar-distance (app 'f 'head) (app 'g 'head))
              tail-distance
              (scalar-distance (map-sum 'A 'f 'tail)
                               (map-sum 'A 'g 'tail))]
          (order-transitive
           (scalar-distance
            (radd (app 'f 'head) (map-sum 'A 'f 'tail))
            (radd (app 'g 'head) (map-sum 'A 'g 'tail)))
           (radd head-distance tail-distance)
           (radd head-distance (map-sum 'A pointwise 'tail))
           (app (function/const* 'nnrat/distance-add-subadditive [])
                (app 'f 'head) (map-sum 'A 'f 'tail)
                (app 'g 'head) (map-sum 'A 'g 'tail))
           (add-left-monotone
            head-distance tail-distance
            (map-sum 'A pointwise 'tail) 'ih))))
       'items)))})
