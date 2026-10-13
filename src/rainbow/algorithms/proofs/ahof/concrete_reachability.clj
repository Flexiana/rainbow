(ns rainbow.algorithms.proofs.ahof.concrete-reachability
  "AHoF V44 Concrete Reachability: the simplest reachability analysis -- push a
  finite set of concrete sample states one step forward through the dynamics and
  collect the images. The one-step reachable set is the map of the transition
  over the current states:

      reach-step step states = [ step x | x in states ].

  Iterating this from the initial set traces a concrete under-approximation of the
  reachable set (exact for the sampled points; the set-valued over-approximation
  is the job of the interval/zonotope propagators). Proved native and axiom-free:
  the reach-step map (built by List.rec producing a list), its cons recurrence,
  and a worked forward image. What is proved is the concrete forward image; the
  sampling density and the abstraction to a covering set are executable concerns.

  Requires nat/nnrat, nnrat/add, and data/List.rec (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.concrete-reachability`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat (function/app (function/const* 'data/List [type-level]) nnrat))
(def step-type (function/arrow nnrat nnrat))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- reach-step [step states]
  (function/app (function/const* 'reachability/reach-step []) step states))

;; Definitions --------------------------------------------------------------

;; reach-step step states = map step states  (the one-step forward image)
(def reach-step-spec
  {:name 'reachability/reach-step :kind :definition :universes []
   :type (function/arrow step-type list-nnrat list-nnrat)
   :value
   (function/lam
    [['step step-type] ['states list-nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] list-nnrat)
     nil-nnrat
     (function/lam
      [['head nnrat] ['tail list-nnrat] ['tail-image list-nnrat]]
      (cons-nnrat (function/app 'step 'head) 'tail-image))
     'states))})

(def definition-specs [reach-step-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- state-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

;; The forward image advances the head and recurses on the tail.
(def reach-step-cons-spec
  {:name 'reachability/reach-step-cons :universes []
   :type (function/forall
          [['step step-type] ['head nnrat] ['tail list-nnrat]]
          (equality list-nnrat
                    (reach-step 'step (cons-nnrat 'head 'tail))
                    (cons-nnrat (function/app 'step 'head)
                                (reach-step 'step 'tail))))
   :value (function/lam
           [['step step-type] ['head nnrat] ['tail list-nnrat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            list-nnrat (reach-step 'step (cons-nnrat 'head 'tail))))})

;; Worked forward image under the +1 dynamics: reach {1,2,3} = {2,3,4}.
(def reach-step-example-spec
  {:name 'reachability/reach-step-example :universes []
   :type (equality list-nnrat
                   (reach-step
                    (function/lam [['x nnrat]] (nnrat-add (whole 1) 'x))
                    (state-list (whole 1) (whole 2) (whole 3)))
                   (state-list (whole 2) (whole 3) (whole 4)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        list-nnrat
                        (reach-step
                         (function/lam [['x nnrat]] (nnrat-add (whole 1) 'x))
                         (state-list (whole 1) (whole 2) (whole 3))))})

;; The empty state set has an empty forward image.
(def reach-step-empty-spec
  {:name 'reachability/reach-step-empty :universes []
   :type (equality list-nnrat
                   (reach-step
                    (function/lam [['x nnrat]] (nnrat-add (whole 1) 'x))
                    nil-nnrat)
                   nil-nnrat)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        list-nnrat
                        (reach-step
                         (function/lam [['x nnrat]] (nnrat-add (whole 1) 'x))
                         nil-nnrat))})

(def theorem-specs
  [reach-step-cons-spec reach-step-example-spec reach-step-empty-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-concrete-reachability (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.concrete-reachability))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
