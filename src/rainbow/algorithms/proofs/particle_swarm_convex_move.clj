(ns rainbow.algorithms.proofs.particle-swarm-convex-move
  "Normalized movement toward a swarm best preserves vector intervals."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.convex-combination :as convex]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args]
  (apply function/app f args))

(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))

(defn- rat-equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))

(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))

(defn- equality [left right]
  (function/equality type-level vector-type left right))

(defn- wsum2 [w-position w-best position best]
  (app (function/const* 'vector/nnrat-wsum2 [])
       w-position w-best position best))

(defn- convex-move [w-position w-best position best]
  (app (function/const* 'swarm/nnrat-convex-move [])
       w-position w-best position best))

(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def convex-move-spec
  {:name 'swarm/nnrat-convex-move
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat vector-type vector-type vector-type)
   :value
   (function/lam
    [['w-position nnrat] ['w-best nnrat]
     ['position vector-type] ['best vector-type]]
    (wsum2 'w-position 'w-best 'position 'best))})

(def convex-move-unfold-spec
  {:name 'swarm/nnrat-convex-move-unfold
   :universes []
   :type
   (function/forall
    [['w-position nnrat] ['w-best nnrat]
     ['position vector-type] ['best vector-type]]
    (equality
     (convex-move 'w-position 'w-best 'position 'best)
     (wsum2 'w-position 'w-best 'position 'best)))
   :value
   (function/lam
    [['w-position nnrat] ['w-best nnrat]
     ['position vector-type] ['best vector-type]]
    (app (function/const* 'equality/reflexive [type-level])
         vector-type
         (convex-move 'w-position 'w-best 'position 'best)))})

(def convex-move-lower-bound-spec
  {:name 'swarm/nnrat-convex-move-lower-bound
   :universes []
   :type
   (function/forall
    [['w-position nnrat] ['w-best nnrat]
     ['position vector-type] ['best vector-type] ['lower vector-type]
     ['normalized
      (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
     ['lower-position (vector-at-most 'lower 'position)]
     ['lower-best (vector-at-most 'lower 'best)]]
    (vector-at-most
     'lower
     (convex-move 'w-position 'w-best 'position 'best)))
   :value
   (function/lam
    [['w-position nnrat] ['w-best nnrat]
     ['position vector-type] ['best vector-type] ['lower vector-type]
     ['normalized
      (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
     ['lower-position (vector-at-most 'lower 'position)]
     ['lower-best (vector-at-most 'lower 'best)]]
    (app (function/const* 'vector/nnrat-convex-lower-bound [])
         'w-position 'w-best 'lower 'position 'best
         'normalized 'lower-position 'lower-best))})

(def convex-move-upper-bound-spec
  {:name 'swarm/nnrat-convex-move-upper-bound
   :universes []
   :type
   (function/forall
    [['w-position nnrat] ['w-best nnrat]
     ['position vector-type] ['best vector-type] ['upper vector-type]
     ['normalized
      (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
     ['position-upper (vector-at-most 'position 'upper)]
     ['best-upper (vector-at-most 'best 'upper)]]
    (vector-at-most
     (convex-move 'w-position 'w-best 'position 'best)
     'upper))
   :value
   (function/lam
    [['w-position nnrat] ['w-best nnrat]
     ['position vector-type] ['best vector-type] ['upper vector-type]
     ['normalized
      (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
     ['position-upper (vector-at-most 'position 'upper)]
     ['best-upper (vector-at-most 'best 'upper)]]
    (app (function/const* 'vector/nnrat-convex-upper-bound [])
         'w-position 'w-best 'position 'best 'upper
         'normalized 'position-upper 'best-upper))})

(def convex-move-between-spec
  (let [moved (convex-move 'w-position 'w-best 'position 'best)
        lower (vector-at-most 'position moved)
        upper (vector-at-most moved 'best)]
    {:name 'swarm/nnrat-convex-move-between-position-and-best
     :universes []
     :type
     (function/forall
      [['w-position nnrat] ['w-best nnrat]
       ['position vector-type] ['best vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['ordered (vector-at-most 'position 'best)]]
      (app (function/const* 'proposition/conjunction []) lower upper))
     :value
     (function/lam
      [['w-position nnrat] ['w-best nnrat]
       ['position vector-type] ['best vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['ordered (vector-at-most 'position 'best)]]
      (conjoin
       lower upper
       (app (function/const* 'swarm/nnrat-convex-move-lower-bound [])
            'w-position 'w-best 'position 'best 'position
            'normalized
            (app (function/const* 'vector/at-most-reflexive []) 'position)
            'ordered)
       (app (function/const* 'swarm/nnrat-convex-move-upper-bound [])
            'w-position 'w-best 'position 'best 'best
            'normalized
            'ordered
            (app (function/const* 'vector/at-most-reflexive []) 'best))))}))

(def convex-move-between-reverse-spec
  (let [moved (convex-move 'w-position 'w-best 'position 'best)
        lower (vector-at-most 'best moved)
        upper (vector-at-most moved 'position)]
    {:name 'swarm/nnrat-convex-move-between-best-and-position
     :universes []
     :type
     (function/forall
      [['w-position nnrat] ['w-best nnrat]
       ['position vector-type] ['best vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['ordered (vector-at-most 'best 'position)]]
      (app (function/const* 'proposition/conjunction []) lower upper))
     :value
     (function/lam
      [['w-position nnrat] ['w-best nnrat]
       ['position vector-type] ['best vector-type]
       ['normalized
        (rat-equivalent (radd 'w-position 'w-best) nnrat-one)]
       ['ordered (vector-at-most 'best 'position)]]
      (conjoin
       lower upper
       (app (function/const* 'swarm/nnrat-convex-move-lower-bound [])
            'w-position 'w-best 'position 'best 'best
            'normalized 'ordered
            (app (function/const* 'vector/at-most-reflexive []) 'best))
       (app (function/const* 'swarm/nnrat-convex-move-upper-bound [])
            'w-position 'w-best 'position 'best 'position
            'normalized
            (app (function/const* 'vector/at-most-reflexive []) 'position)
            'ordered)))}))

(def definition-specs [convex-move-spec])

(def theorem-specs
  [convex-move-unfold-spec
   convex-move-lower-bound-spec
   convex-move-upper-bound-spec
   convex-move-between-spec
   convex-move-between-reverse-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.convex-combination])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :particle-swarm-convex-move (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.particle-swarm-convex-move))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
