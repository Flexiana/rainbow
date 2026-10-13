(ns rainbow.algorithms.proofs.particle-swarm-projected-trajectory
  "Box-projected particle updates and finite-horizon trajectory boundedness."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.particle-swarm :as swarm]
            [rainbow.math.linear.vector.uniform-clamp :as clamp]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- succ [value]
  (function/app successor value))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- signed-at-most [left right]
  (function/app (function/const* 'signed/at-most []) left right))

(defn- in-band [lower upper values]
  (function/app (function/const* 'vector/in-band []) lower upper values))

(defn- uniform-clamp [lower upper values]
  (function/app (function/const* 'vector/uniform-clamp [])
                lower upper values))

(defn- swarm-step [w c1 c2 velocity position pbest gbest]
  (function/app (function/const* 'swarm/step [])
                w c1 c2 velocity position pbest gbest))

(defn- projected-step
  [lower upper w c1 c2 velocity position pbest gbest]
  (function/app (function/const* 'swarm/projected-step [])
                lower upper w c1 c2 velocity position pbest gbest))

(defn- projected-trajectory [lower upper update initial steps]
  (function/app (function/const* 'swarm/projected-trajectory [])
                lower upper update initial steps))

(def projected-step-spec
  {:name 'swarm/projected-step
   :kind :definition
   :universes []
   :type
   (function/arrow
    signed signed
    nnrat nnrat nnrat
    vector-type vector-type vector-type vector-type
    vector-type)
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['w nnrat] ['c1 nnrat] ['c2 nnrat]
     ['velocity vector-type] ['position vector-type]
     ['pbest vector-type] ['gbest vector-type]]
    (uniform-clamp
     'lower 'upper
     (swarm-step 'w 'c1 'c2 'velocity 'position 'pbest 'gbest)))})

(def projected-trajectory-spec
  {:name 'swarm/projected-trajectory
   :kind :definition
   :universes []
   :type
   (function/arrow
    signed signed
    (function/arrow nat vector-type vector-type)
    vector-type nat vector-type)
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['update (function/arrow nat vector-type vector-type)]
     ['initial vector-type] ['steps nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] vector-type)
     'initial
     (function/lam
      [['previous-step nat] ['previous-position vector-type]]
      (uniform-clamp
       'lower 'upper
       (function/app 'update 'previous-step 'previous-position)))
     'steps))})

(def projected-step-unfold-spec
  {:name 'swarm/projected-step-unfold
   :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['w nnrat] ['c1 nnrat] ['c2 nnrat]
     ['velocity vector-type] ['position vector-type]
     ['pbest vector-type] ['gbest vector-type]]
    (equality
     vector-type
     (projected-step 'lower 'upper 'w 'c1 'c2
                     'velocity 'position 'pbest 'gbest)
     (uniform-clamp
      'lower 'upper
      (swarm-step 'w 'c1 'c2 'velocity 'position 'pbest 'gbest))))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['w nnrat] ['c1 nnrat] ['c2 nnrat]
     ['velocity vector-type] ['position vector-type]
     ['pbest vector-type] ['gbest vector-type]]
    (function/app
     (function/const* 'equality/reflexive [type-level])
     vector-type
     (projected-step 'lower 'upper 'w 'c1 'c2
                     'velocity 'position 'pbest 'gbest)))})

(def projected-step-in-band-spec
  {:name 'swarm/projected-step-in-band
   :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['ordered (signed-at-most 'lower 'upper)]
     ['w nnrat] ['c1 nnrat] ['c2 nnrat]
     ['velocity vector-type] ['position vector-type]
     ['pbest vector-type] ['gbest vector-type]]
    (in-band
     'lower 'upper
     (projected-step 'lower 'upper 'w 'c1 'c2
                     'velocity 'position 'pbest 'gbest)))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['ordered (signed-at-most 'lower 'upper)]
     ['w nnrat] ['c1 nnrat] ['c2 nnrat]
     ['velocity vector-type] ['position vector-type]
     ['pbest vector-type] ['gbest vector-type]]
    (function/app
     (function/const* 'vector/uniform-clamp-in-band [])
     'lower 'upper 'ordered
     (swarm-step 'w 'c1 'c2 'velocity 'position 'pbest 'gbest)))})

(def projected-trajectory-zero-spec
  {:name 'swarm/projected-trajectory-zero
   :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['update (function/arrow nat vector-type vector-type)]
     ['initial vector-type]]
    (equality
     vector-type
     (projected-trajectory 'lower 'upper 'update 'initial zero)
     'initial))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['update (function/arrow nat vector-type vector-type)]
     ['initial vector-type]]
    (function/app
     (function/const* 'equality/reflexive [type-level])
     vector-type
     (projected-trajectory 'lower 'upper 'update 'initial zero)))})

(def projected-trajectory-successor-spec
  (let [previous
        (projected-trajectory 'lower 'upper 'update 'initial 'steps)]
    {:name 'swarm/projected-trajectory-successor
     :universes []
     :type
     (function/forall
      [['lower signed] ['upper signed]
       ['update (function/arrow nat vector-type vector-type)]
       ['initial vector-type] ['steps nat]]
      (equality
       vector-type
       (projected-trajectory
        'lower 'upper 'update 'initial (succ 'steps))
       (uniform-clamp
        'lower 'upper
        (function/app 'update 'steps previous))))
     :value
     (function/lam
      [['lower signed] ['upper signed]
       ['update (function/arrow nat vector-type vector-type)]
       ['initial vector-type] ['steps nat]]
      (function/app
       (function/const* 'equality/reflexive [type-level])
       vector-type
       (projected-trajectory
        'lower 'upper 'update 'initial (succ 'steps))))}))

(def projected-trajectory-successor-in-band-spec
  (let [previous
        (projected-trajectory 'lower 'upper 'update 'initial 'steps)]
    {:name 'swarm/projected-trajectory-successor-in-band
     :universes []
     :type
     (function/forall
      [['lower signed] ['upper signed]
       ['ordered (signed-at-most 'lower 'upper)]
       ['update (function/arrow nat vector-type vector-type)]
       ['initial vector-type] ['steps nat]]
      (in-band
       'lower 'upper
       (projected-trajectory
        'lower 'upper 'update 'initial (succ 'steps))))
     :value
     (function/lam
      [['lower signed] ['upper signed]
       ['ordered (signed-at-most 'lower 'upper)]
       ['update (function/arrow nat vector-type vector-type)]
       ['initial vector-type] ['steps nat]]
      (function/app
       (function/const* 'vector/uniform-clamp-in-band [])
       'lower 'upper 'ordered
       (function/app 'update 'steps previous)))}))

(def projected-trajectory-in-band-spec
  (let [iterated
        (fn [steps]
          (projected-trajectory 'lower 'upper 'update 'initial steps))
        motive
        (function/lam
         [['steps nat]]
         (in-band 'lower 'upper (iterated 'steps)))]
    {:name 'swarm/projected-trajectory-in-band
     :universes []
     :type
     (function/forall
      [['lower signed] ['upper signed]
       ['ordered (signed-at-most 'lower 'upper)]
       ['update (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['initial-in-band (in-band 'lower 'upper 'initial)]
       ['steps nat]]
      (function/app motive 'steps))
     :value
     (function/lam
      [['lower signed] ['upper signed]
       ['ordered (signed-at-most 'lower 'upper)]
       ['update (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['initial-in-band (in-band 'lower 'upper 'initial)]
       ['steps nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       'initial-in-band
       (function/lam
        [['previous nat]
         ['ignored (function/app motive 'previous)]]
        (function/app
         (function/const* 'swarm/projected-trajectory-successor-in-band [])
         'lower 'upper 'ordered 'update 'initial 'previous))
       'steps))}))

(def definition-specs
  [projected-step-spec projected-trajectory-spec])

(def theorem-specs
  [projected-step-unfold-spec
   projected-step-in-band-spec
   projected-trajectory-zero-spec
   projected-trajectory-successor-spec
   projected-trajectory-successor-in-band-spec
   projected-trajectory-in-band-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector rainbow.algorithms.proofs.particle-swarm rainbow.math.linear.vector.uniform-clamp])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :particle-swarm-projected-trajectory (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.particle-swarm-projected-trajectory))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
