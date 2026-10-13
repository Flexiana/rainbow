(ns rainbow.math.sets.preimage-lattice
  "Preimages preserve intersection, union, and difference by exact reuse."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def V [:param 'v])
(def data-level [:succ U])
(def target-data-level [:succ V])
(def type-u [:sort data-level])
(def type-v [:sort target-data-level])

(defn- set-of [level element]
  (function/app (function/const* 'set/Set [level]) element))

(defn- preimage [mapping target]
  (function/app (function/const* 'set/preimage [U V])
                'A 'B mapping target))

(defn- subset [small large]
  (function/app (function/const* 'set/subset [U])
                'A small large))

(defn- binary-set [operator level element left right]
  (function/app (function/const* operator [level])
                element left right))

(defn- binary-preimage-laws
  [operator forward-name backward-name equivalence-name]
  (let [set-b (set-of V 'B)
        target-combined
        (binary-set operator V 'B 'left 'right)
        preimage-combined (preimage 'mapping target-combined)
        left-preimage (preimage 'mapping 'left)
        right-preimage (preimage 'mapping 'right)
        combined-preimages
        (binary-set operator U 'A left-preimage right-preimage)
        forward (subset preimage-combined combined-preimages)
        backward (subset combined-preimages preimage-combined)]
    [{:name forward-name
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v]
        ['mapping (function/arrow 'A 'B)]
        ['left set-b] ['right set-b]]
       forward)
      :value
      (function/lam
       [['A type-u] ['B type-v]
        ['mapping (function/arrow 'A 'B)]
        ['left set-b] ['right set-b]
        ['value 'A]
        ['member (function/app preimage-combined 'value)]]
       'member)}
     {:name backward-name
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v]
        ['mapping (function/arrow 'A 'B)]
        ['left set-b] ['right set-b]]
       backward)
      :value
      (function/lam
       [['A type-u] ['B type-v]
        ['mapping (function/arrow 'A 'B)]
        ['left set-b] ['right set-b]
        ['value 'A]
        ['member (function/app combined-preimages 'value)]]
       'member)}
     {:name equivalence-name
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v]
        ['mapping (function/arrow 'A 'B)]
        ['left set-b] ['right set-b]]
       (proposition/conjunction forward backward))
      :value
      (function/lam
       [['A type-u] ['B type-v]
        ['mapping (function/arrow 'A 'B)]
        ['left set-b] ['right set-b]]
       (function/app
        (function/const* 'proposition/conjoin [])
        forward backward
        (function/app (function/const* forward-name [U V])
                      'A 'B 'mapping 'left 'right)
        (function/app (function/const* backward-name [U V])
                      'A 'B 'mapping 'left 'right)))}]))

(def intersection-specs
  (binary-preimage-laws
   'set/intersection
   'set/preimage-intersection-subset-intersection-preimages
   'set/intersection-preimages-subset-preimage-intersection
   'set/preimage-intersection-equivalent-intersection-preimages))

(def union-specs
  (binary-preimage-laws
   'set/union
   'set/preimage-union-subset-union-preimages
   'set/union-preimages-subset-preimage-union
   'set/preimage-union-equivalent-union-preimages))

(def difference-specs
  (binary-preimage-laws
   'set/difference
   'set/preimage-difference-subset-difference-preimages
   'set/difference-preimages-subset-preimage-difference
   'set/preimage-difference-equivalent-difference-preimages))

(def theorem-specs
  (vec (concat intersection-specs union-specs difference-specs)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.set])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :set-preimage-lattice theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.sets.preimage-lattice))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
