(ns rainbow.math.sets.image-certificates
  "Constructive image/target inclusions from certified set maps."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.sets.inverse-certificates :as inverse]))

(def U [:param 'u])
(def V [:param 'v])
(def data-level [:succ U])
(def target-data-level [:succ V])
(def type-u [:sort data-level])
(def type-v [:sort target-data-level])

(defn- set-of [level element]
  (function/app (function/const* 'set/Set [level]) element))

(defn- image [mapping source]
  (function/app (function/const* 'set/image [U V])
                'A 'B mapping source))

(defn- subset [level element small large]
  (function/app (function/const* 'set/subset [level])
                element small large))

(defn- maps-to [source-level target-level source-element target-element
                 mapping source target]
  (function/app (function/const* 'set/maps-to
                                 [source-level target-level])
                source-element target-element mapping source target))

(defn- injective-on [mapping source]
  (function/app (function/const* 'set/injective-on [U V])
                'A 'B mapping source))

(defn- surjective-on [mapping source target]
  (function/app (function/const* 'set/surjective-on [U V])
                'A 'B mapping source target))

(defn- bijective-on [mapping source target]
  (function/app (function/const* 'set/bijective-on [U V])
                'A 'B mapping source target))

(defn- inverse-on [backward forward source target]
  (function/app (function/const* 'set/inverse-on [U V])
                'A 'B backward forward source target))

(def image-subset-of-maps-to-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        mapped (image 'mapping 'source)
        maps (maps-to U V 'A 'B 'mapping 'source 'target)
        result (subset V 'B mapped 'target)]
    {:name 'set/image-subset-of-maps-to
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['maps-evidence maps]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['maps-evidence maps]
       ['value 'B]
       ['image-member (function/app mapped 'value)]]
      (let [fiber
            (function/lam
             [['input 'A]]
             (proposition/conjunction
              (function/app 'source 'input)
              (function/equality target-data-level 'B
                                 (function/app 'mapping 'input) 'value)))]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A fiber (function/app 'target 'value) 'image-member
         (function/lam
          [['input 'A]
           ['fiber-evidence (function/app fiber 'input)]]
          (let [source-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app 'source 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'fiber-evidence)
                same
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app 'source 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'fiber-evidence)]
            (function/app
             same
             (function/lam
              [['candidate 'B]] (function/app 'target 'candidate))
             (function/app 'maps-evidence 'input source-member)))))))}))

(def target-subset-image-of-surjective-on-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        mapped (image 'mapping 'source)
        surjection (surjective-on 'mapping 'source 'target)
        result (subset V 'B 'target mapped)]
    {:name 'set/target-subset-image-of-surjective-on
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['surjection-evidence surjection]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['surjection-evidence surjection]
       ['value 'B]
       ['target-member (function/app 'target 'value)]]
      (function/app 'surjection-evidence 'value 'target-member))}))

(def image-target-equivalent-of-maps-surjective-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        mapped (image 'mapping 'source)
        maps (maps-to U V 'A 'B 'mapping 'source 'target)
        surjection (surjective-on 'mapping 'source 'target)
        image-subset (subset V 'B mapped 'target)
        target-subset (subset V 'B 'target mapped)
        result (proposition/conjunction image-subset target-subset)]
    {:name 'set/image-target-equivalent-of-maps-surjective
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['maps-evidence maps]
       ['surjection-evidence surjection]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['maps-evidence maps]
       ['surjection-evidence surjection]]
      (function/app
       (function/const* 'proposition/conjoin [])
       image-subset target-subset
       (function/app
        (function/const* 'set/image-subset-of-maps-to [U V])
        'A 'B 'mapping 'source 'target 'maps-evidence)
       (function/app
        (function/const* 'set/target-subset-image-of-surjective-on [U V])
        'A 'B 'mapping 'source 'target 'surjection-evidence)))}))

(def image-target-equivalent-of-bijective-on-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        mapped (image 'mapping 'source)
        maps (maps-to U V 'A 'B 'mapping 'source 'target)
        injection (injective-on 'mapping 'source)
        surjection (surjective-on 'mapping 'source 'target)
        bijection (bijective-on 'mapping 'source 'target)
        result
        (proposition/conjunction
         (subset V 'B mapped 'target)
         (subset V 'B 'target mapped))]
    {:name 'set/image-target-equivalent-of-bijective-on
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['bijection-evidence bijection]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['bijection-evidence bijection]]
      (let [maps-evidence
            (function/app
             (function/const* 'proposition/left [])
             maps (proposition/conjunction injection surjection)
             'bijection-evidence)
            injective-surjective
            (function/app
             (function/const* 'proposition/right [])
             maps (proposition/conjunction injection surjection)
             'bijection-evidence)
            surjection-evidence
            (function/app
             (function/const* 'proposition/right [])
             injection surjection injective-surjective)]
        (function/app
         (function/const*
          'set/image-target-equivalent-of-maps-surjective [U V])
         'A 'B 'mapping 'source 'target
         maps-evidence surjection-evidence)))}))

(def image-target-equivalent-of-inverse-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        mapped (image 'forward 'source)
        forward-maps
        (maps-to U V 'A 'B 'forward 'source 'target)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        inverse-evidence
        (inverse-on 'backward 'forward 'source 'target)
        result
        (proposition/conjunction
         (subset V 'B mapped 'target)
         (subset V 'B 'target mapped))]
    {:name 'set/image-target-equivalent-of-inverse
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]]
      (function/app
       (function/const* 'set/image-target-equivalent-of-bijective-on [U V])
       'A 'B 'forward 'source 'target
       (function/app
        (function/const* 'set/bijective-on-of-inverse [U V])
        'A 'B 'forward 'backward 'source 'target
        'forward-maps 'backward-maps 'inverse-evidence)))}))

(def theorem-specs
  [image-subset-of-maps-to-spec
   target-subset-image-of-surjective-on-spec
   image-target-equivalent-of-maps-surjective-spec
   image-target-equivalent-of-bijective-on-spec
   image-target-equivalent-of-inverse-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      inverse/extend-environment
      (support/extend-with :set-image-certificates theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
