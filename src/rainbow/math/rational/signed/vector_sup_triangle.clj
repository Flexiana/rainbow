(ns rainbow.math.rational.signed.vector-sup-triangle
  "Triangle inequality for equal-shaped signed-rational list vectors.

  The list representation intentionally gives distance zero when either input
  is empty, so a global triangle law over arbitrary unequal lengths is false.
  Two adjacent `vector/same-shape` hypotheses rule out exactly those mismatch
  cases.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance-triangle :as scalar]
            [rainbow.math.rational.signed.vector-sup-distance :as sup]
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
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- triangle-goal [left middle right]
  (sle (sup-distance left right)
       (add (sup-distance left middle)
            (sup-distance middle right))))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- add-monotone [left left-prime right right-prime first second]
  (app (function/const* 'signed/add-monotone [])
       left left-prime right right-prime first second))
(defn- max-left [left right]
  (app (function/const* 'signed/max-upper-left []) left right))
(defn- max-right [left right]
  (app (function/const* 'signed/max-upper-right []) left right))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))

(defn- zero-triangle []
  (let [double-zero (add signed-zero signed-zero)]
    (app
     (function/const* 'signed/equivalent-to-at-most [])
     signed-zero double-zero
     (equivalent-symmetric
      double-zero signed-zero
      (app (function/const* 'signed/add-zero-right []) signed-zero)))))

(def sup-distance-triangle-same-shape-spec
  {:name 'vector/sup-distance-triangle-same-shape :universes []
   :type
   (function/forall
    [['left vector-type] ['middle vector-type] ['right vector-type]
     ['left-middle (same-shape 'left 'middle)]
     ['middle-right (same-shape 'middle 'right)]]
    (triangle-goal 'left 'middle 'right))
   :value
   (function/lam
    [['left vector-type] ['middle vector-type] ['right vector-type]
     ['left-middle (same-shape 'left 'middle)]
     ['middle-right (same-shape 'middle 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-middle vector-type]
             ['current-right vector-type]
             ['current-left-middle
              (same-shape 'current-left 'current-middle)]
             ['current-middle-right
              (same-shape 'current-middle 'current-right)]]
            (triangle-goal
             'current-left 'current-middle 'current-right)))
          outer-base
          (let [empty (nil-vector)
                middle-motive
                (function/lam
                 [['current-middle vector-type]]
                 (function/forall
                  [['current-right vector-type]
                   ['current-left-middle
                    (same-shape empty 'current-middle)]
                   ['current-middle-right
                    (same-shape 'current-middle 'current-right)]]
                  (triangle-goal empty 'current-middle 'current-right)))]
            (function/lam
             [['current-middle vector-type]]
             (list-rec
              middle-motive
              (let [right-motive
                    (function/lam
                     [['current-right vector-type]]
                     (function/forall
                      [['current-left-middle
                        (same-shape empty empty)]
                       ['current-middle-right
                        (same-shape empty 'current-right)]]
                      (triangle-goal empty empty 'current-right)))]
                (function/lam
                 [['current-right vector-type]]
                 (list-rec
                  right-motive
                  (function/lam
                   [['current-left-middle (same-shape empty empty)]
                    ['current-middle-right (same-shape empty empty)]]
                   (zero-triangle))
                  (function/lam
                   [['right-head signed] ['right-tail vector-type]
                    ['ignored (app right-motive 'right-tail)]]
                   (function/lam
                    [['current-left-middle (same-shape empty empty)]
                     ['current-middle-right
                      (same-shape
                       empty (cons-vector 'right-head 'right-tail))]]
                    (absurd
                     (triangle-goal
                      empty empty (cons-vector 'right-head 'right-tail))
                     'current-middle-right)))
                  'current-right)))
              (function/lam
               [['middle-head signed] ['middle-tail vector-type]
                ['ignored (app middle-motive 'middle-tail)]]
               (let [current-middle
                     (cons-vector 'middle-head 'middle-tail)]
                 (function/lam
                  [['current-right vector-type]
                   ['current-left-middle
                    (same-shape empty current-middle)]
                   ['current-middle-right
                    (same-shape current-middle 'current-right)]]
                  (absurd
                   (triangle-goal empty current-middle 'current-right)
                   'current-left-middle))))
              'current-middle)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-triangle (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 middle-motive
                 (function/lam
                  [['current-middle vector-type]]
                  (function/forall
                   [['current-right vector-type]
                    ['current-left-middle
                     (same-shape current-left 'current-middle)]
                    ['current-middle-right
                     (same-shape 'current-middle 'current-right)]]
                   (triangle-goal
                    current-left 'current-middle 'current-right)))]
             (function/lam
              [['current-middle vector-type]]
              (list-rec
               middle-motive
               (function/lam
                [['current-right vector-type]
                 ['current-left-middle
                  (same-shape current-left (nil-vector))]
                 ['current-middle-right
                  (same-shape (nil-vector) 'current-right)]]
                (absurd
                 (triangle-goal current-left (nil-vector) 'current-right)
                 'current-left-middle))
               (function/lam
                [['middle-head signed] ['middle-tail vector-type]
                 ['ignored-middle (app middle-motive 'middle-tail)]]
                (let [current-middle
                      (cons-vector 'middle-head 'middle-tail)
                      right-motive
                      (function/lam
                       [['current-right vector-type]]
                       (function/forall
                        [['current-left-middle
                          (same-shape current-left current-middle)]
                         ['current-middle-right
                          (same-shape current-middle 'current-right)]]
                        (triangle-goal
                         current-left current-middle 'current-right)))]
                  (function/lam
                   [['current-right vector-type]]
                   (list-rec
                    right-motive
                    (function/lam
                     [['current-left-middle
                       (same-shape current-left current-middle)]
                      ['current-middle-right
                       (same-shape current-middle (nil-vector))]]
                     (absurd
                      (triangle-goal
                       current-left current-middle (nil-vector))
                      'current-middle-right))
                    (function/lam
                     [['right-head signed] ['right-tail vector-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (function/lam
                      [['current-left-middle
                        (same-shape current-left current-middle)]
                       ['current-middle-right
                        (same-shape
                         current-middle
                         (cons-vector 'right-head 'right-tail))]]
                      (let [head-zero (veq signed-zero signed-zero)
                            left-tail-middle
                            (same-shape 'left-tail 'middle-tail)
                            middle-tail-right
                            (same-shape 'middle-tail 'right-tail)
                            tail-left-middle
                            (proposition-right
                             head-zero left-tail-middle
                             'current-left-middle)
                            tail-middle-right
                            (proposition-right
                             head-zero middle-tail-right
                             'current-middle-right)
                            head-left-middle
                            (scalar-distance 'left-head 'middle-head)
                            head-middle-right
                            (scalar-distance 'middle-head 'right-head)
                            head-left-right
                            (scalar-distance 'left-head 'right-head)
                            tail-left-middle-distance
                            (sup-distance 'left-tail 'middle-tail)
                            tail-middle-right-distance
                            (sup-distance 'middle-tail 'right-tail)
                            tail-left-right-distance
                            (sup-distance 'left-tail 'right-tail)
                            left-middle-distance
                            (maximum
                             head-left-middle tail-left-middle-distance)
                            middle-right-distance
                            (maximum
                             head-middle-right tail-middle-right-distance)
                            threshold
                            (add left-middle-distance
                                 middle-right-distance)
                            head-legs-bound
                            (add-monotone
                             head-left-middle left-middle-distance
                             head-middle-right middle-right-distance
                             (max-left
                              head-left-middle tail-left-middle-distance)
                             (max-left
                              head-middle-right tail-middle-right-distance))
                            head-bound
                            (order-transitive
                             head-left-right
                             (add head-left-middle head-middle-right)
                             threshold
                             (app
                              (function/const* 'signed/distance-triangle [])
                              'left-head 'middle-head 'right-head)
                             head-legs-bound)
                            tail-legs-bound
                            (add-monotone
                             tail-left-middle-distance left-middle-distance
                             tail-middle-right-distance middle-right-distance
                             (max-right
                              head-left-middle tail-left-middle-distance)
                             (max-right
                              head-middle-right tail-middle-right-distance))
                            tail-bound
                            (order-transitive
                             tail-left-right-distance
                             (add tail-left-middle-distance
                                  tail-middle-right-distance)
                             threshold
                             (app
                              'tail-triangle
                              'middle-tail 'right-tail
                              tail-left-middle tail-middle-right)
                             tail-legs-bound)]
                        (app
                         (function/const*
                          'vector/sup-distance-cons-bounded [])
                         'left-head 'left-tail
                         'right-head 'right-tail
                         threshold head-bound tail-bound))))
                    'current-right))))
               'current-middle))))]
      (app
       (list-rec outer-motive outer-base outer-step 'left)
       'middle 'right 'left-middle 'middle-right)))})

(def definition-specs [])
(def theorem-specs [sup-distance-triangle-same-shape-spec])

(defn extend-environment [env]
  (-> env
      scalar/extend-environment
      sup/extend-environment
      shape/extend-environment
      (support/extend-with :signed-vector-sup-triangle theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
