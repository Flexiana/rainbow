(ns rainbow.algorithms.proofs.particle-swarm-global-best
  "Verified finite-swarm global-best selection and best-so-far monotonicity."
  (:require [rainbow.math.finite.rational-argmin :as argmin]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [zero-level]) element))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [zero-level])
                element source value))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- rational-at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- finite-argmin [positions initial objective]
  (function/app
   (function/const* 'decision/finite-nnrat-argmin [zero-level])
   vector-type positions initial objective))

(defn- select-min [objective previous candidate]
  (function/app
   (function/const* 'decision/nnrat-select-min [zero-level])
   vector-type objective previous candidate))

(defn- global-best [objective positions initial]
  (function/app (function/const* 'swarm/nnrat-global-best [])
                objective positions initial))

(defn- best-so-far [objective previous candidate]
  (function/app (function/const* 'swarm/nnrat-best-so-far [])
                objective previous candidate))

(def global-best-spec
  {:name 'swarm/nnrat-global-best
   :kind :definition
   :universes []
   :type
   (function/arrow
    (function/arrow vector-type nnrat)
    (exact-finset-of vector-type)
    vector-type
    vector-type)
   :value
   (function/lam
    [['objective (function/arrow vector-type nnrat)]
     ['positions (exact-finset-of vector-type)]
     ['initial vector-type]]
    (finite-argmin 'positions 'initial 'objective))})

(def best-so-far-spec
  {:name 'swarm/nnrat-best-so-far
   :kind :definition
   :universes []
   :type
   (function/arrow
    (function/arrow vector-type nnrat)
    vector-type vector-type vector-type)
   :value
   (function/lam
    [['objective (function/arrow vector-type nnrat)]
     ['previous vector-type]
     ['candidate vector-type]]
    (select-min 'objective 'previous 'candidate))})

(def global-best-unfold-spec
  {:name 'swarm/nnrat-global-best-unfold
   :universes []
   :type
   (function/forall
    [['objective (function/arrow vector-type nnrat)]
     ['positions (exact-finset-of vector-type)]
     ['initial vector-type]]
    (equality vector-type
              (global-best 'objective 'positions 'initial)
              (finite-argmin 'positions 'initial 'objective)))
   :value
   (function/lam
    [['objective (function/arrow vector-type nnrat)]
     ['positions (exact-finset-of vector-type)]
     ['initial vector-type]]
    (function/app (function/const* 'equality/reflexive [type-level])
                  vector-type
                  (global-best 'objective 'positions 'initial)))})

(def global-best-member-spec
  (let [result (global-best 'objective 'positions 'initial)]
    {:name 'swarm/nnrat-global-best-is-member
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['positions (exact-finset-of vector-type)]
       ['initial vector-type]
       ['initial-member
        (source-membership vector-type 'positions 'initial)]]
      (source-membership vector-type 'positions result))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['positions (exact-finset-of vector-type)]
       ['initial vector-type]
       ['initial-member
        (source-membership vector-type 'positions 'initial)]]
      (function/app
       (function/const* 'decision/finite-nnrat-argmin-is-member [zero-level])
       vector-type 'positions 'initial 'objective 'initial-member))}))

(def global-best-dominates-spec
  (let [result (global-best 'objective 'positions 'initial)]
    {:name 'swarm/nnrat-global-best-dominates
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['positions (exact-finset-of vector-type)]
       ['initial vector-type]
       ['candidate vector-type]
       ['candidate-member
        (source-membership vector-type 'positions 'candidate)]]
      (rational-at-most (function/app 'objective result)
                        (function/app 'objective 'candidate)))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['positions (exact-finset-of vector-type)]
       ['initial vector-type]
       ['candidate vector-type]
       ['candidate-member
        (source-membership vector-type 'positions 'candidate)]]
      (function/app
       (function/const* 'decision/finite-nnrat-argmin-dominates [zero-level])
       vector-type 'positions 'initial 'objective
       'candidate 'candidate-member))}))

(def best-so-far-unfold-spec
  {:name 'swarm/nnrat-best-so-far-unfold
   :universes []
   :type
   (function/forall
    [['objective (function/arrow vector-type nnrat)]
     ['previous vector-type]
     ['candidate vector-type]]
    (equality vector-type
              (best-so-far 'objective 'previous 'candidate)
              (select-min 'objective 'previous 'candidate)))
   :value
   (function/lam
    [['objective (function/arrow vector-type nnrat)]
     ['previous vector-type]
     ['candidate vector-type]]
    (function/app (function/const* 'equality/reflexive [type-level])
                  vector-type
                  (best-so-far 'objective 'previous 'candidate)))})

(def best-so-far-choice-spec
  (let [result (best-so-far 'objective 'previous 'candidate)]
    {:name 'swarm/nnrat-best-so-far-is-previous-or-candidate
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['previous vector-type]
       ['candidate vector-type]]
      (proposition/disjunction
       (equality vector-type result 'previous)
       (equality vector-type result 'candidate)))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['previous vector-type]
       ['candidate vector-type]]
      (function/app
       (function/const*
        'decision/nnrat-select-min-is-left-or-right [zero-level])
       vector-type 'objective 'previous 'candidate))}))

(def best-so-far-bounds-previous-spec
  (let [result (best-so-far 'objective 'previous 'candidate)]
    {:name 'swarm/nnrat-best-so-far-bounds-previous
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['previous vector-type]
       ['candidate vector-type]]
      (rational-at-most (function/app 'objective result)
                        (function/app 'objective 'previous)))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['previous vector-type]
       ['candidate vector-type]]
      (function/app
       (function/const* 'decision/nnrat-select-min-bounds-left [zero-level])
       vector-type 'objective 'previous 'candidate))}))

(def best-so-far-bounds-candidate-spec
  (let [result (best-so-far 'objective 'previous 'candidate)]
    {:name 'swarm/nnrat-best-so-far-bounds-candidate
     :universes []
     :type
     (function/forall
      [['objective (function/arrow vector-type nnrat)]
       ['previous vector-type]
       ['candidate vector-type]]
      (rational-at-most (function/app 'objective result)
                        (function/app 'objective 'candidate)))
     :value
     (function/lam
      [['objective (function/arrow vector-type nnrat)]
       ['previous vector-type]
       ['candidate vector-type]]
      (function/app
       (function/const* 'decision/nnrat-select-min-bounds-right [zero-level])
       vector-type 'objective 'previous 'candidate))}))

(def definition-specs [global-best-spec best-so-far-spec])

(def theorem-specs
  [global-best-unfold-spec
   global-best-member-spec
   global-best-dominates-spec
   best-so-far-unfold-spec
   best-so-far-choice-spec
   best-so-far-bounds-previous-spec
   best-so-far-bounds-candidate-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      argmin/extend-environment
      (support/extend-with :particle-swarm-global-best
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
