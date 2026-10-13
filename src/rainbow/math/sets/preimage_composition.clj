(ns rainbow.math.sets.preimage-composition
  "Identity and composition laws for set preimages."
  (:require [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def data-level [:succ U])
(def middle-data-level [:succ V])
(def target-data-level [:succ W])
(def type-u [:sort data-level])
(def type-v [:sort middle-data-level])
(def type-w [:sort target-data-level])

(defn- set-of [level element]
  (function/app (function/const* 'set/Set [level]) element))

(defn- preimage [source-level target-level source-element target-element
                 mapping target]
  (function/app (function/const* 'set/preimage
                                 [source-level target-level])
                source-element target-element mapping target))

(defn- subset [level element small large]
  (function/app (function/const* 'set/subset [level])
                element small large))

(defn- identity-map []
  (function/app (function/const* 'function/identity [data-level]) 'A))

(defn- composed [outer inner]
  (function/app
   (function/const* 'function/compose
                    [data-level middle-data-level target-data-level])
   'A 'B 'C outer inner))

(def preimage-identity-subset-source-spec
  (let [set-a (set-of U 'A)
        identity-preimage
        (preimage U U 'A 'A (identity-map) 'source)]
    {:name 'set/preimage-identity-subset-source
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source set-a]]
      (subset U 'A identity-preimage 'source))
     :value
     (function/lam
      [['A type-u] ['source set-a]
       ['value 'A]
       ['member (function/app identity-preimage 'value)]]
      'member)}))

(def source-subset-preimage-identity-spec
  (let [set-a (set-of U 'A)
        identity-preimage
        (preimage U U 'A 'A (identity-map) 'source)]
    {:name 'set/source-subset-preimage-identity
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source set-a]]
      (subset U 'A 'source identity-preimage))
     :value
     (function/lam
      [['A type-u] ['source set-a]
       ['value 'A]
       ['member (function/app 'source 'value)]]
      'member)}))

(def preimage-identity-equivalent-source-spec
  (let [set-a (set-of U 'A)
        identity-preimage
        (preimage U U 'A 'A (identity-map) 'source)
        forward (subset U 'A identity-preimage 'source)
        backward (subset U 'A 'source identity-preimage)]
    {:name 'set/preimage-identity-equivalent-source
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source set-a]]
      (proposition/conjunction forward backward))
     :value
     (function/lam
      [['A type-u] ['source set-a]]
      (function/app
       (function/const* 'proposition/conjoin [])
       forward backward
       (function/app
        (function/const* 'set/preimage-identity-subset-source [U])
        'A 'source)
       (function/app
        (function/const* 'set/source-subset-preimage-identity [U])
        'A 'source)))}))

(def preimage-compose-subset-nested-preimage-spec
  (let [set-c (set-of W 'C)
        outer-preimage
        (preimage V W 'B 'C 'outer 'target)
        nested-preimage
        (preimage U V 'A 'B 'inner outer-preimage)
        composed-preimage
        (preimage U W 'A 'C (composed 'outer 'inner) 'target)]
    {:name 'set/preimage-compose-subset-nested-preimage
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['target set-c]]
      (subset U 'A composed-preimage nested-preimage))
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['target set-c]
       ['value 'A]
       ['member (function/app composed-preimage 'value)]]
      'member)}))

(def nested-preimage-subset-preimage-compose-spec
  (let [set-c (set-of W 'C)
        outer-preimage
        (preimage V W 'B 'C 'outer 'target)
        nested-preimage
        (preimage U V 'A 'B 'inner outer-preimage)
        composed-preimage
        (preimage U W 'A 'C (composed 'outer 'inner) 'target)]
    {:name 'set/nested-preimage-subset-preimage-compose
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['target set-c]]
      (subset U 'A nested-preimage composed-preimage))
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['target set-c]
       ['value 'A]
       ['member (function/app nested-preimage 'value)]]
      'member)}))

(def preimage-compose-equivalent-nested-preimage-spec
  (let [set-c (set-of W 'C)
        outer-preimage
        (preimage V W 'B 'C 'outer 'target)
        nested-preimage
        (preimage U V 'A 'B 'inner outer-preimage)
        composed-preimage
        (preimage U W 'A 'C (composed 'outer 'inner) 'target)
        forward (subset U 'A composed-preimage nested-preimage)
        backward (subset U 'A nested-preimage composed-preimage)]
    {:name 'set/preimage-compose-equivalent-nested-preimage
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['target set-c]]
      (proposition/conjunction forward backward))
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['target set-c]]
      (function/app
       (function/const* 'proposition/conjoin [])
       forward backward
       (function/app
        (function/const*
         'set/preimage-compose-subset-nested-preimage [U V W])
        'A 'B 'C 'inner 'outer 'target)
       (function/app
        (function/const*
         'set/nested-preimage-subset-preimage-compose [U V W])
        'A 'B 'C 'inner 'outer 'target)))}))

(def theorem-specs
  [preimage-identity-subset-source-spec
   source-subset-preimage-identity-spec
   preimage-identity-equivalent-source-spec
   preimage-compose-subset-nested-preimage-spec
   nested-preimage-subset-preimage-compose-spec
   preimage-compose-equivalent-nested-preimage-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      finite-set/extend-environment
      (support/extend-with :set-preimage-composition theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
