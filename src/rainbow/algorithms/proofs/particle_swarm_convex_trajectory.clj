(ns rainbow.algorithms.proofs.particle-swarm-convex-trajectory
  "Finite normalized consensus trajectories remain inside invariant intervals."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.particle-swarm-convex-move :as convex-move]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args]
  (apply function/app f args))

(defn- succ [value]
  (app successor value))

(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))

(defn- rat-equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))

(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))

(defn- equality [left right]
  (function/equality type-level vector-type left right))

(defn- convex-step [w-position w-best position best]
  (app (function/const* 'swarm/nnrat-convex-move [])
       w-position w-best position best))

(defn- convex-trajectory [w-position w-best bests initial steps]
  (app (function/const* 'swarm/nnrat-convex-trajectory [])
       w-position w-best bests initial steps))

(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def convex-trajectory-spec
  {:name 'swarm/nnrat-convex-trajectory
   :kind :definition
   :universes []
   :type
   (function/arrow
    nnrat nnrat
    (function/arrow nat vector-type)
    vector-type nat vector-type)
   :value
   (function/lam
    [['w-position nnrat] ['w-best nnrat]
     ['bests (function/arrow nat vector-type)]
     ['initial vector-type] ['steps nat]]
    (app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] vector-type)
     'initial
     (function/lam
      [['previous-step nat] ['previous-position vector-type]]
      (convex-step
       'w-position 'w-best
       'previous-position
       (app 'bests 'previous-step)))
     'steps))})

(def convex-trajectory-zero-spec
  {:name 'swarm/nnrat-convex-trajectory-zero
   :universes []
   :type
   (function/forall
    [['w-position nnrat] ['w-best nnrat]
     ['bests (function/arrow nat vector-type)]
     ['initial vector-type]]
    (equality
     (convex-trajectory 'w-position 'w-best 'bests 'initial zero)
     'initial))
   :value
   (function/lam
    [['w-position nnrat] ['w-best nnrat]
     ['bests (function/arrow nat vector-type)]
     ['initial vector-type]]
    (app (function/const* 'equality/reflexive [type-level])
         vector-type
         (convex-trajectory 'w-position 'w-best 'bests 'initial zero)))})

(def convex-trajectory-successor-spec
  (let [previous
        (convex-trajectory 'w-position 'w-best 'bests 'initial 'steps)]
    {:name 'swarm/nnrat-convex-trajectory-successor
     :universes []
     :type
     (function/forall
      [['w-position nnrat] ['w-best nnrat]
       ['bests (function/arrow nat vector-type)]
       ['initial vector-type] ['steps nat]]
      (equality
       (convex-trajectory
        'w-position 'w-best 'bests 'initial (succ 'steps))
       (convex-step
        'w-position 'w-best previous (app 'bests 'steps))))
     :value
     (function/lam
      [['w-position nnrat] ['w-best nnrat]
       ['bests (function/arrow nat vector-type)]
       ['initial vector-type] ['steps nat]]
      (app
       (function/const* 'equality/reflexive [type-level])
       vector-type
       (convex-trajectory
        'w-position 'w-best 'bests 'initial (succ 'steps))))}))

(def convex-trajectory-lower-bound-spec
  (let [iterated
        (fn [steps]
          (convex-trajectory
           'w-position 'w-best 'bests 'initial steps))
        motive
        (function/lam
         [['steps nat]]
         (vector-at-most 'lower (iterated 'steps)))]
    {:name 'swarm/nnrat-convex-trajectory-lower-bound
     :universes []
     :type
     (function/forall
      [['w-position nnrat] ['w-best nnrat]
       ['bests (function/arrow nat vector-type)]
       ['initial vector-type] ['lower vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['initial-lower (vector-at-most 'lower 'initial)]
       ['best-lower
        (function/forall
         [['step nat]]
         (vector-at-most 'lower (app 'bests 'step)))]
       ['steps nat]]
      (function/app motive 'steps))
     :value
     (function/lam
      [['w-position nnrat] ['w-best nnrat]
       ['bests (function/arrow nat vector-type)]
       ['initial vector-type] ['lower vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['initial-lower (vector-at-most 'lower 'initial)]
       ['best-lower
        (function/forall
         [['step nat]]
         (vector-at-most 'lower (app 'bests 'step)))]
       ['steps nat]]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       'initial-lower
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        (app
         (function/const* 'swarm/nnrat-convex-move-lower-bound [])
         'w-position 'w-best
         (iterated 'previous) (app 'bests 'previous) 'lower
         'normalized
         'induction-hypothesis
         (app 'best-lower 'previous)))
       'steps))}))

(def convex-trajectory-upper-bound-spec
  (let [iterated
        (fn [steps]
          (convex-trajectory
           'w-position 'w-best 'bests 'initial steps))
        motive
        (function/lam
         [['steps nat]]
         (vector-at-most (iterated 'steps) 'upper))]
    {:name 'swarm/nnrat-convex-trajectory-upper-bound
     :universes []
     :type
     (function/forall
      [['w-position nnrat] ['w-best nnrat]
       ['bests (function/arrow nat vector-type)]
       ['initial vector-type] ['upper vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['initial-upper (vector-at-most 'initial 'upper)]
       ['best-upper
        (function/forall
         [['step nat]]
         (vector-at-most (app 'bests 'step) 'upper))]
       ['steps nat]]
      (function/app motive 'steps))
     :value
     (function/lam
      [['w-position nnrat] ['w-best nnrat]
       ['bests (function/arrow nat vector-type)]
       ['initial vector-type] ['upper vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['initial-upper (vector-at-most 'initial 'upper)]
       ['best-upper
        (function/forall
         [['step nat]]
         (vector-at-most (app 'bests 'step) 'upper))]
       ['steps nat]]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       'initial-upper
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        (app
         (function/const* 'swarm/nnrat-convex-move-upper-bound [])
         'w-position 'w-best
         (iterated 'previous) (app 'bests 'previous) 'upper
         'normalized
         'induction-hypothesis
         (app 'best-upper 'previous)))
       'steps))}))

(def convex-trajectory-in-interval-spec
  (let [result
        (convex-trajectory 'w-position 'w-best 'bests 'initial 'steps)
        lower-claim (vector-at-most 'lower result)
        upper-claim (vector-at-most result 'upper)]
    {:name 'swarm/nnrat-convex-trajectory-in-interval
     :universes []
     :type
     (function/forall
      [['w-position nnrat] ['w-best nnrat]
       ['bests (function/arrow nat vector-type)]
       ['initial vector-type] ['lower vector-type] ['upper vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['initial-lower (vector-at-most 'lower 'initial)]
       ['initial-upper (vector-at-most 'initial 'upper)]
       ['best-lower
        (function/forall
         [['step nat]]
         (vector-at-most 'lower (app 'bests 'step)))]
       ['best-upper
        (function/forall
         [['step nat]]
         (vector-at-most (app 'bests 'step) 'upper))]
       ['steps nat]]
      (app (function/const* 'proposition/conjunction [])
           lower-claim upper-claim))
     :value
     (function/lam
      [['w-position nnrat] ['w-best nnrat]
       ['bests (function/arrow nat vector-type)]
       ['initial vector-type] ['lower vector-type] ['upper vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['initial-lower (vector-at-most 'lower 'initial)]
       ['initial-upper (vector-at-most 'initial 'upper)]
       ['best-lower
        (function/forall
         [['step nat]]
         (vector-at-most 'lower (app 'bests 'step)))]
       ['best-upper
        (function/forall
         [['step nat]]
         (vector-at-most (app 'bests 'step) 'upper))]
       ['steps nat]]
      (conjoin
       lower-claim upper-claim
       (app
        (function/const* 'swarm/nnrat-convex-trajectory-lower-bound [])
        'w-position 'w-best 'bests 'initial 'lower
        'normalized 'initial-lower 'best-lower 'steps)
       (app
        (function/const* 'swarm/nnrat-convex-trajectory-upper-bound [])
        'w-position 'w-best 'bests 'initial 'upper
        'normalized 'initial-upper 'best-upper 'steps)))}))

(def definition-specs [convex-trajectory-spec])

(def theorem-specs
  [convex-trajectory-zero-spec
   convex-trajectory-successor-spec
   convex-trajectory-lower-bound-spec
   convex-trajectory-upper-bound-spec
   convex-trajectory-in-interval-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      convex-move/extend-environment
      (support/extend-with :particle-swarm-convex-trajectory
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
