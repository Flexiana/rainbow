(ns rainbow.algorithms.proofs.particle-swarm-best-iterate
  "Finite-horizon best-so-far recurrence and objective monotonicity."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.particle-swarm-global-best :as global-best]
            [rainbow.math.logic.proposition :as proposition]))

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

(defn- rational-at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- best-so-far [objective previous candidate]
  (function/app (function/const* 'swarm/nnrat-best-so-far [])
                objective previous candidate))

(defn- best-iterate [objective proposal initial steps]
  (function/app (function/const* 'swarm/nnrat-best-iterate [])
                objective proposal initial steps))

(def best-iterate-spec
  {:name 'swarm/nnrat-best-iterate
   :kind :definition
   :universes []
   :type
   (function/arrow
    (function/arrow vector-type nnrat)
    (function/arrow nat vector-type vector-type)
    vector-type nat vector-type)
   :value
   (function/lam
    [['objective (function/arrow vector-type nnrat)]
     ['proposal (function/arrow nat vector-type vector-type)]
     ['initial vector-type]
     ['steps nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] vector-type)
     'initial
     (function/lam
      [['previous-step nat] ['previous-best vector-type]]
      (best-so-far
       'objective
       'previous-best
       (function/app 'proposal 'previous-step 'previous-best)))
     'steps))})

(def best-iterate-zero-spec
  {:name 'swarm/nnrat-best-iterate-zero
   :universes []
   :type
   (function/forall
    [['objective (function/arrow vector-type nnrat)]
     ['proposal (function/arrow nat vector-type vector-type)]
     ['initial vector-type]]
    (equality vector-type
              (best-iterate 'objective 'proposal 'initial zero)
              'initial))
   :value
   (function/lam
    [['objective (function/arrow vector-type nnrat)]
     ['proposal (function/arrow nat vector-type vector-type)]
     ['initial vector-type]]
    (function/app (function/const* 'equality/reflexive [type-level])
                  vector-type
                  (best-iterate 'objective 'proposal 'initial zero)))})

(def best-iterate-successor-spec
  (let [previous (best-iterate 'objective 'proposal 'initial 'steps)]
    {:name 'swarm/nnrat-best-iterate-successor
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (equality
       vector-type
       (best-iterate 'objective 'proposal 'initial (succ 'steps))
       (best-so-far 'objective previous
                    (function/app 'proposal 'steps previous))))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (function/app
       (function/const* 'equality/reflexive [type-level])
       vector-type
       (best-iterate 'objective 'proposal 'initial (succ 'steps))))}))

(def best-iterate-successor-choice-spec
  (let [previous (best-iterate 'objective 'proposal 'initial 'steps)
        candidate (function/app 'proposal 'steps previous)
        next (best-iterate 'objective 'proposal 'initial (succ 'steps))]
    {:name 'swarm/nnrat-best-iterate-successor-is-previous-or-proposal
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (proposition/disjunction
       (equality vector-type next previous)
       (equality vector-type next candidate)))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (function/app
       (function/const*
        'swarm/nnrat-best-so-far-is-previous-or-candidate [])
       'objective previous candidate))}))

(def best-iterate-successor-bounds-previous-spec
  (let [previous (best-iterate 'objective 'proposal 'initial 'steps)
        candidate (function/app 'proposal 'steps previous)
        next (best-iterate 'objective 'proposal 'initial (succ 'steps))]
    {:name 'swarm/nnrat-best-iterate-successor-bounds-previous
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (rational-at-most (function/app 'objective next)
                        (function/app 'objective previous)))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (function/app
       (function/const* 'swarm/nnrat-best-so-far-bounds-previous [])
       'objective previous candidate))}))

(def best-iterate-successor-bounds-proposal-spec
  (let [previous (best-iterate 'objective 'proposal 'initial 'steps)
        candidate (function/app 'proposal 'steps previous)
        next (best-iterate 'objective 'proposal 'initial (succ 'steps))]
    {:name 'swarm/nnrat-best-iterate-successor-bounds-proposal
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (rational-at-most (function/app 'objective next)
                        (function/app 'objective candidate)))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (function/app
       (function/const* 'swarm/nnrat-best-so-far-bounds-candidate [])
       'objective previous candidate))}))

(def best-iterate-bounds-initial-spec
  (let [iterated (fn [steps]
                   (best-iterate 'objective 'proposal 'initial steps))
        motive
        (function/lam
         [['steps nat]]
         (rational-at-most
          (function/app 'objective (iterated 'steps))
          (function/app 'objective 'initial)))]
    {:name 'swarm/nnrat-best-iterate-bounds-initial
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (function/app motive 'steps))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['proposal (function/arrow nat vector-type vector-type)]
       ['initial vector-type]
       ['steps nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/app
        (function/const* 'nnrat/at-most-reflexive [])
        (function/app 'objective 'initial))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        (function/app
         (function/const* 'nnrat/at-most-transitive [])
         (function/app 'objective (iterated (succ 'previous)))
         (function/app 'objective (iterated 'previous))
         (function/app 'objective 'initial)
         (function/app
          (function/const*
           'swarm/nnrat-best-iterate-successor-bounds-previous [])
          'objective 'proposal 'initial 'previous)
         'induction-hypothesis))
       'steps))}))

(def definition-specs [best-iterate-spec])

(def theorem-specs
  [best-iterate-zero-spec
   best-iterate-successor-spec
   best-iterate-successor-choice-spec
   best-iterate-successor-bounds-previous-spec
   best-iterate-successor-bounds-proposal-spec
   best-iterate-bounds-initial-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.particle-swarm-global-best])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :particle-swarm-best-iterate (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.particle-swarm-best-iterate))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
