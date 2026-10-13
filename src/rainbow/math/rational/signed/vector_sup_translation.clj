(ns rainbow.math.rational.signed.vector-sup-translation
  "Fixed-shape translation invariance of signed-list sup distance.

  Vector addition truncates to the shorter list, so common translation is a
  metric law only when the prefix has the shape of both translated vectors.
  A three-list structural proof lifts scalar distance translation through
  signed maximum.  Vector-add commutativity and sup-distance congruence derive
  the right-translation orientation.  Native, kernel-checked, and axiom-free
  on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance-translation :as scalar]
            [rainbow.math.rational.signed.vector-sup-congruence :as congruence]
            [rainbow.math.linear.vector.add-order :as add-order]
            [rainbow.math.linear.vector.shape-cancellation :as shape]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & xs] (apply function/app f xs))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(defn- translation-goal [prefix left right]
  (veq
   (sup-distance (vector-add prefix left)
                 (vector-add prefix right))
   (sup-distance left right)))

(def sup-distance-add-left-same-shape-spec
  {:name 'vector/sup-distance-add-left-same-shape :universes []
   :type
   (function/forall
    [['prefix vector-type] ['left vector-type] ['right vector-type]
     ['prefix-left (same-shape 'prefix 'left)]
     ['prefix-right (same-shape 'prefix 'right)]]
    (translation-goal 'prefix 'left 'right))
   :value
   (function/lam
    [['prefix vector-type] ['left vector-type] ['right vector-type]
     ['prefix-left (same-shape 'prefix 'left)]
     ['prefix-right (same-shape 'prefix 'right)]]
    (let [outer-motive
          (function/lam
           [['current-prefix vector-type]]
           (function/forall
            [['current-left vector-type] ['current-right vector-type]
             ['current-prefix-left
              (same-shape 'current-prefix 'current-left)]
             ['current-prefix-right
              (same-shape 'current-prefix 'current-right)]]
            (translation-goal
             'current-prefix 'current-left 'current-right)))
          outer-base
          (let [empty (nil-vector)
                left-motive
                (function/lam
                 [['current-left vector-type]]
                 (function/forall
                  [['current-right vector-type]
                   ['current-prefix-left
                    (same-shape empty 'current-left)]
                   ['current-prefix-right
                    (same-shape empty 'current-right)]]
                  (translation-goal empty 'current-left 'current-right)))]
            (function/lam
             [['current-left vector-type]]
             (list-rec
              left-motive
              (let [right-motive
                    (function/lam
                     [['current-right vector-type]]
                     (function/forall
                      [['current-prefix-left
                        (same-shape empty empty)]
                       ['current-prefix-right
                        (same-shape empty 'current-right)]]
                      (translation-goal empty empty 'current-right)))]
                (function/lam
                 [['current-right vector-type]]
                 (list-rec
                  right-motive
                  (function/lam
                   [['current-prefix-left (same-shape empty empty)]
                    ['current-prefix-right (same-shape empty empty)]]
                   (equivalent-reflexive signed-zero))
                  (function/lam
                   [['right-head signed] ['right-tail vector-type]
                    ['ignored-right (app right-motive 'right-tail)]]
                   (function/lam
                    [['current-prefix-left (same-shape empty empty)]
                     ['current-prefix-right
                      (same-shape
                       empty (cons-vector 'right-head 'right-tail))]]
                    (absurd
                     (translation-goal
                      empty empty (cons-vector 'right-head 'right-tail))
                     'current-prefix-right)))
                  'current-right)))
              (function/lam
               [['left-head signed] ['left-tail vector-type]
                ['ignored-left (app left-motive 'left-tail)]]
               (let [current-left (cons-vector 'left-head 'left-tail)]
                 (function/lam
                  [['current-right vector-type]
                   ['current-prefix-left
                    (same-shape empty current-left)]
                   ['current-prefix-right
                    (same-shape empty 'current-right)]]
                  (absurd
                   (translation-goal empty current-left 'current-right)
                   'current-prefix-left))))
              'current-left)))
          outer-step
          (function/lam
           [['prefix-head signed] ['prefix-tail vector-type]
            ['tail-translation (app outer-motive 'prefix-tail)]]
           (let [current-prefix
                 (cons-vector 'prefix-head 'prefix-tail)
                 left-motive
                 (function/lam
                  [['current-left vector-type]]
                  (function/forall
                   [['current-right vector-type]
                    ['current-prefix-left
                     (same-shape current-prefix 'current-left)]
                    ['current-prefix-right
                     (same-shape current-prefix 'current-right)]]
                   (translation-goal
                    current-prefix 'current-left 'current-right)))]
             (function/lam
              [['current-left vector-type]]
              (list-rec
               left-motive
               (function/lam
                [['current-right vector-type]
                 ['current-prefix-left
                  (same-shape current-prefix (nil-vector))]
                 ['current-prefix-right
                  (same-shape current-prefix 'current-right)]]
                (absurd
                 (translation-goal
                  current-prefix (nil-vector) 'current-right)
                 'current-prefix-left))
               (function/lam
                [['left-head signed] ['left-tail vector-type]
                 ['ignored-left (app left-motive 'left-tail)]]
                (let [current-left (cons-vector 'left-head 'left-tail)
                      right-motive
                      (function/lam
                       [['current-right vector-type]]
                       (function/forall
                        [['current-prefix-left
                          (same-shape current-prefix current-left)]
                         ['current-prefix-right
                          (same-shape current-prefix 'current-right)]]
                        (translation-goal
                         current-prefix current-left 'current-right)))]
                  (function/lam
                   [['current-right vector-type]]
                   (list-rec
                    right-motive
                    (function/lam
                     [['current-prefix-left
                       (same-shape current-prefix current-left)]
                      ['current-prefix-right
                       (same-shape current-prefix (nil-vector))]]
                     (absurd
                      (translation-goal
                       current-prefix current-left (nil-vector))
                      'current-prefix-right))
                    (function/lam
                     [['right-head signed] ['right-tail vector-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (let [current-right
                           (cons-vector 'right-head 'right-tail)]
                       (function/lam
                        [['current-prefix-left
                          (same-shape current-prefix current-left)]
                         ['current-prefix-right
                          (same-shape current-prefix current-right)]]
                        (let [head-zero (veq signed-zero signed-zero)
                              prefix-tail-left
                              (same-shape 'prefix-tail 'left-tail)
                              prefix-tail-right
                              (same-shape 'prefix-tail 'right-tail)
                              tail-prefix-left
                              (proposition-right
                               head-zero prefix-tail-left
                               'current-prefix-left)
                              tail-prefix-right
                              (proposition-right
                               head-zero prefix-tail-right
                               'current-prefix-right)]
                          (app
                           (function/const*
                            'signed/max-respects-equivalence [])
                           (scalar-distance
                            (signed-add 'prefix-head 'left-head)
                            (signed-add 'prefix-head 'right-head))
                           (sup-distance
                            (vector-add 'prefix-tail 'left-tail)
                            (vector-add 'prefix-tail 'right-tail))
                           (scalar-distance 'left-head 'right-head)
                           (sup-distance 'left-tail 'right-tail)
                           (app
                            (function/const* 'signed/distance-add-left [])
                            'prefix-head 'left-head 'right-head)
                           (app
                            'tail-translation
                            'left-tail 'right-tail
                            tail-prefix-left tail-prefix-right))))))
                    'current-right))))
               'current-left))))]
      (app
       (list-rec outer-motive outer-base outer-step 'prefix)
       'left 'right 'prefix-left 'prefix-right)))})

(def sup-distance-add-right-same-shape-spec
  {:name 'vector/sup-distance-add-right-same-shape :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['suffix vector-type]
     ['suffix-left (same-shape 'suffix 'left)]
     ['suffix-right (same-shape 'suffix 'right)]]
    (veq
     (sup-distance (vector-add 'left 'suffix)
                   (vector-add 'right 'suffix))
     (sup-distance 'left 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['suffix vector-type]
     ['suffix-left (same-shape 'suffix 'left)]
     ['suffix-right (same-shape 'suffix 'right)]]
    (let [start
          (sup-distance (vector-add 'left 'suffix)
                        (vector-add 'right 'suffix))
          commuted
          (sup-distance (vector-add 'suffix 'left)
                        (vector-add 'suffix 'right))
          finish (sup-distance 'left 'right)]
      (equivalent-transitive
       start commuted finish
       (app
        (function/const*
         'vector/sup-distance-respects-equivalence [])
        (vector-add 'left 'suffix) (vector-add 'suffix 'left)
        (vector-add 'right 'suffix) (vector-add 'suffix 'right)
        (app (function/const* 'vector/add-commutative [])
             'left 'suffix)
        (app (function/const* 'vector/add-commutative [])
             'right 'suffix))
       (app
        (function/const*
         'vector/sup-distance-add-left-same-shape [])
        'suffix 'left 'right 'suffix-left 'suffix-right))))})

(def definition-specs [])
(def theorem-specs
  [sup-distance-add-left-same-shape-spec
   sup-distance-add-right-same-shape-spec])

(defn extend-environment [env]
  (-> env
      scalar/extend-environment
      congruence/extend-environment
      add-order/extend-environment
      shape/extend-environment
      (support/extend-with :signed-vector-sup-translation theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
