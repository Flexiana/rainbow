(ns rainbow.math.nat.distance-radius
  "Natural distance is the least symmetric additive radius.

      distance a b <= r
        iff
      a <= b + r  and  b <= a + r

  The forward direction combines the existing endpoint bounds with monotonicity.
  The reverse direction strips matching successors from the two additive bounds
  until one endpoint is zero.  This is the arithmetic interface needed to lift
  computational `nat/distance` through exact-rational cross products.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.at-most-cancellation :as cancellation]
            [rainbow.math.nat.contraction :as contraction]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def one (function/app successor zero))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- add [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- distance [left right]
  (app (function/const* 'nat/distance []) left right))
(defn- at-most [left right]
  (app (function/const* 'nat/at-most []) left right))
(defn- equality [left right]
  (function/equality type-level nat left right))
(defn- at-most-transitive [left middle right first second]
  (app (function/const* 'nat/at-most-transitive [])
       left middle right first second))
(defn- rewrite-right [left right replacement same ordered]
  (app (function/const* 'nat/at-most-rewrite-right [])
       left right replacement same ordered))
(defn- add-left-cancel [left right prefix ordered]
  (app (function/const* 'nat/at-most-add-left-cancel [])
       left right prefix ordered))
(defn- add-right-monotone [suffix left right ordered]
  (app (function/const* 'nat/add-right-monotone [])
       suffix left right ordered))

(def distance-at-most-of-additive-bounds-spec
  (let [goal
        (fn [left right radius]
          (function/forall
           [['left-bound (at-most left (add right radius))]
            ['right-bound (at-most right (add left radius))]]
           (at-most (distance left right) radius)))
        outer-motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat] ['radius nat]]
          (goal 'left 'right 'radius)))]
    {:name 'nat/distance-at-most-of-additive-bounds
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat] ['radius nat]
       ['left-bound (at-most 'left (add 'right 'radius))]
       ['right-bound (at-most 'right (add 'left 'radius))]]
      (at-most (distance 'left 'right) 'radius))
     :value
     (function/lam
      [['left nat]]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       outer-motive
       (function/lam
        [['right nat] ['radius nat]
         ['ignored-left (at-most zero (add 'right 'radius))]
         ['right-bound (at-most 'right (add zero 'radius))]]
        'right-bound)
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (app outer-motive 'left-previous)]
         ['right nat]]
        (let [left-now (succ 'left-previous)
              right-motive
              (function/lam
               [['current-right nat]]
               (function/forall
                [['radius nat]]
                (goal left-now 'current-right 'radius)))]
          (app
           (function/const* 'data/Nat.rec [zero-level])
           right-motive
           (function/lam
            [['radius nat]
             ['left-bound (at-most left-now (add zero 'radius))]
             ['ignored-right (at-most zero (add left-now 'radius))]]
            'left-bound)
           (function/lam
            [['right-previous nat]
             ['ignored (app right-motive 'right-previous)]
             ['radius nat]
             ['left-bound
              (at-most left-now (add (succ 'right-previous) 'radius))]
             ['right-bound
              (at-most (succ 'right-previous) (add left-now 'radius))]]
            (app
             'induction-hypothesis 'right-previous 'radius
             (add-left-cancel
              'left-previous (add 'right-previous 'radius)
              one 'left-bound)
             (add-left-cancel
              'right-previous (add 'left-previous 'radius)
              one 'right-bound)))
           'right)))
       'left))}))

(def additive-bounds-of-distance-at-most-spec
  {:name 'nat/additive-bounds-of-distance-at-most
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat] ['radius nat]
     ['bounded (at-most (distance 'left 'right) 'radius)]]
    (proposition/conjunction
     (at-most 'left (add 'right 'radius))
     (at-most 'right (add 'left 'radius))))
   :value
   (function/lam
    [['left nat] ['right nat] ['radius nat]
     ['bounded (at-most (distance 'left 'right) 'radius)]]
    (let [delta (distance 'left 'right)
          delta-right (add delta 'right)
          radius-right (add 'radius 'right)
          right-radius (add 'right 'radius)
          delta-left (add delta 'left)
          radius-left (add 'radius 'left)
          left-radius (add 'left 'radius)
          delta-right-bounded
          (add-right-monotone 'right delta 'radius 'bounded)
          delta-left-bounded
          (add-right-monotone 'left delta 'radius 'bounded)
          delta-right-to-goal
          (rewrite-right
           delta-right radius-right right-radius
           (app (function/const* 'nat/add-commutative [])
                'radius 'right)
           delta-right-bounded)
          delta-left-to-goal
          (rewrite-right
           delta-left radius-left left-radius
           (app (function/const* 'nat/add-commutative [])
                'radius 'left)
           delta-left-bounded)
          left-bound
          (at-most-transitive
           'left delta-right right-radius
           (app (function/const* 'nat/distance-first-bound [])
                'left 'right)
           delta-right-to-goal)
          right-bound
          (at-most-transitive
           'right delta-left left-radius
           (app (function/const* 'nat/distance-left-bound [])
                'left 'right)
           delta-left-to-goal)]
      (app (function/const* 'proposition/conjoin [])
           (at-most 'left right-radius)
           (at-most 'right left-radius)
           left-bound right-bound)))})

(def distance-at-most-iff-additive-bounds-spec
  {:name 'nat/distance-at-most-iff-additive-bounds
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat] ['radius nat]]
    (proposition/equivalence
     (at-most (distance 'left 'right) 'radius)
     (proposition/conjunction
      (at-most 'left (add 'right 'radius))
      (at-most 'right (add 'left 'radius)))))
   :value
   (function/lam
    [['left nat] ['right nat] ['radius nat]]
    (let [bounded (at-most (distance 'left 'right) 'radius)
          left-bound (at-most 'left (add 'right 'radius))
          right-bound (at-most 'right (add 'left 'radius))
          bounds (proposition/conjunction left-bound right-bound)]
      (app
       (function/const* 'proposition/equivalence-intro [])
       bounded bounds
       (function/lam
        [['evidence bounded]]
        (app (function/const* 'nat/additive-bounds-of-distance-at-most [])
             'left 'right 'radius 'evidence))
       (function/lam
        [['evidence bounds]]
        (app
         (function/const* 'nat/distance-at-most-of-additive-bounds [])
         'left 'right 'radius
         (app (function/const* 'proposition/left [])
              left-bound right-bound 'evidence)
         (app (function/const* 'proposition/right [])
              left-bound right-bound 'evidence))))))})

(def definition-specs [])
(def theorem-specs
  [distance-at-most-of-additive-bounds-spec
   additive-bounds-of-distance-at-most-spec
   distance-at-most-iff-additive-bounds-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.contraction rainbow.math.nat.at-most-cancellation])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :nat-distance-radius theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.nat.distance-radius))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
