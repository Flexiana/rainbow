(ns rainbow.algorithms.proofs.particle-swarm
  "AHoF O45 Particle Swarm Optimization: the per-particle velocity and position
  update over genuinely n-dimensional vector state. Each particle carries a
  position and a velocity vector; the velocity is pulled by inertia toward its
  own momentum, cognitively toward its personal best, and socially toward the
  swarm's global best:

      v' = w*v + c1*(pbest - x) + c2*(gbest - x)
      x' = x + v'

  Every term is an operation from the finite-vector capability (scale, subtract,
  add), so this is the first optimizer whose state is a true vector rather than a
  scalar or a fixed-arity pair. The coefficients are general nonnegative
  rationals; the stochastic weights of the textbook algorithm are supplied as
  concrete rationals in the worked instance, so what is proved here is the
  deterministic update recurrence and a worked two-dimensional step, not the
  stochastic convergence (which stays an executable-only concern).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.particle-swarm`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.vector :as dep-finite-vector]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

;; Vector-capability term builders (from rainbow.math.finite.vector).
(defn- vector-add [left right]
  (function/app (function/const* 'vector/add []) left right))
(defn- vector-subtract [left right]
  (function/app (function/const* 'vector/subtract []) left right))
(defn- vector-scale [rate value]
  (function/app (function/const* 'vector/scale []) rate value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- swarm-velocity-update [w c1 c2 velocity position pbest gbest]
  (function/app (function/const* 'swarm/velocity-update [])
                w c1 c2 velocity position pbest gbest))
(defn- swarm-position-update [position velocity]
  (function/app (function/const* 'swarm/position-update []) position velocity))
(defn- swarm-step [w c1 c2 velocity position pbest gbest]
  (function/app (function/const* 'swarm/step [])
                w c1 c2 velocity position pbest gbest))

;; Definitions --------------------------------------------------------------

;; v' = w*v + c1*(pbest - x) + c2*(gbest - x)
(def velocity-update-spec
  {:name 'swarm/velocity-update :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat
                         vector-type vector-type vector-type vector-type
                         vector-type)
   :value (function/lam
           [['w nnrat] ['c1 nnrat] ['c2 nnrat]
            ['velocity vector-type] ['position vector-type]
            ['pbest vector-type] ['gbest vector-type]]
           (vector-add
            (vector-scale 'w 'velocity)
            (vector-add
             (vector-scale 'c1 (vector-subtract 'pbest 'position))
             (vector-scale 'c2 (vector-subtract 'gbest 'position)))))})

;; x' = x + v'
(def position-update-spec
  {:name 'swarm/position-update :kind :definition :universes []
   :type (function/arrow vector-type vector-type vector-type)
   :value (function/lam [['position vector-type] ['velocity vector-type]]
                        (vector-add 'position 'velocity))})

;; One full particle update: move by the freshly computed velocity.
(def step-spec
  {:name 'swarm/step :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat
                         vector-type vector-type vector-type vector-type
                         vector-type)
   :value (function/lam
           [['w nnrat] ['c1 nnrat] ['c2 nnrat]
            ['velocity vector-type] ['position vector-type]
            ['pbest vector-type] ['gbest vector-type]]
           (swarm-position-update
            'position
            (swarm-velocity-update 'w 'c1 'c2 'velocity 'position
                                   'pbest 'gbest)))})

(def definition-specs [velocity-update-spec position-update-spec step-spec])

;; Theorems -----------------------------------------------------------------

;; The position update unfolds to a vector addition.
(def position-update-unfold-spec
  {:name 'swarm/position-update-unfold :universes []
   :type (function/forall
          [['position vector-type] ['velocity vector-type]]
          (equality vector-type
                    (swarm-position-update 'position 'velocity)
                    (vector-add 'position 'velocity)))
   :value (function/lam [['position vector-type] ['velocity vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (swarm-position-update 'position 'velocity)))})

;; A full step unfolds to moving by the freshly computed velocity.
(def step-unfold-spec
  {:name 'swarm/step-unfold :universes []
   :type (function/forall
          [['w nnrat] ['c1 nnrat] ['c2 nnrat]
           ['velocity vector-type] ['position vector-type]
           ['pbest vector-type] ['gbest vector-type]]
          (equality vector-type
                    (swarm-step 'w 'c1 'c2 'velocity 'position 'pbest 'gbest)
                    (swarm-position-update
                     'position
                     (swarm-velocity-update 'w 'c1 'c2 'velocity 'position
                                            'pbest 'gbest))))
   :value (function/lam
           [['w nnrat] ['c1 nnrat] ['c2 nnrat]
            ['velocity vector-type] ['position vector-type]
            ['pbest vector-type] ['gbest vector-type]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            vector-type
            (swarm-step 'w 'c1 'c2 'velocity 'position 'pbest 'gbest)))})

;; Worked two-dimensional step ----------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nnrat-numeral [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat []) (nnrat-numeral n)))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (function/app (function/const* 'data/nil [type-level]) signed)
          (reverse components)))

;; Worked instance: unit weights, particle at the origin, velocity [1,0],
;; personal best [2,0], global best [0,2].
;;   v' = 1*[1,0] + 1*([2,0]-[0,0]) + 1*([0,2]-[0,0]) = [1,0]+[2,0]+[0,2] = [3,2]
;;   x' = [0,0] + [3,2] = [3,2]
;; The particle sits at the origin so every difference keeps a zero negative
;; part, and the whole trajectory reduces to a canonical vector by reflexivity.
(def one-rational (nnrat-numeral 1))
(def origin (make-vector (signed-numeral 0) (signed-numeral 0)))
(def start-velocity (make-vector (signed-numeral 1) (signed-numeral 0)))
(def personal-best (make-vector (signed-numeral 2) (signed-numeral 0)))
(def global-best (make-vector (signed-numeral 0) (signed-numeral 2)))
(def updated-vector (make-vector (signed-numeral 3) (signed-numeral 2)))

(def velocity-update-example-spec
  {:name 'swarm/velocity-update-example :universes []
   :type (equality vector-type
                   (swarm-velocity-update one-rational one-rational one-rational
                                          start-velocity origin
                                          personal-best global-best)
                   updated-vector)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (swarm-velocity-update one-rational one-rational
                                               one-rational start-velocity origin
                                               personal-best global-best))})

(def position-update-example-spec
  {:name 'swarm/position-update-example :universes []
   :type (equality vector-type
                   (swarm-position-update origin updated-vector)
                   updated-vector)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (swarm-position-update origin updated-vector))})

(def step-example-spec
  {:name 'swarm/step-example :universes []
   :type (equality vector-type
                   (swarm-step one-rational one-rational one-rational
                               start-velocity origin personal-best global-best)
                   updated-vector)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (swarm-step one-rational one-rational one-rational
                                    start-velocity origin personal-best
                                    global-best))})

(def theorem-specs
  [position-update-unfold-spec step-unfold-spec
   velocity-update-example-spec position-update-example-spec
   step-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :particle-swarm (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.particle-swarm))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
