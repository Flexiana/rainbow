(ns rainbow.math.sets.image-preimage-adjunction
  "The constructive image/preimage Galois connection for set inclusion."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.sets.image-certificates :as image-certificates]))

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

(defn- preimage [mapping target]
  (function/app (function/const* 'set/preimage [U V])
                'A 'B mapping target))

(defn- subset [level element small large]
  (function/app (function/const* 'set/subset [level])
                element small large))

(defn- image-fiber [mapping source value]
  (function/lam
   [['candidate 'A]]
   (proposition/conjunction
    (function/app source 'candidate)
    (function/equality target-data-level 'B
                       (function/app mapping 'candidate) value))))

(def image-subset-of-source-subset-preimage-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        mapped (image 'mapping 'source)
        pulled-back (preimage 'mapping 'target)
        source-inclusion (subset U 'A 'source pulled-back)
        image-inclusion (subset V 'B mapped 'target)]
    {:name 'set/image-subset-of-source-subset-preimage
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['source-inclusion source-inclusion]]
      image-inclusion)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['source-inclusion source-inclusion]]
      (let [maps-evidence
            (function/lam
             [['input 'A :implicit]
              ['source-member (function/app 'source 'input)]]
             (function/app
              'source-inclusion 'input 'source-member))]
        (function/app
         (function/const* 'set/image-subset-of-maps-to [U V])
         'A 'B 'mapping 'source 'target maps-evidence)))}))

(def source-subset-preimage-of-image-subset-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        mapped (image 'mapping 'source)
        pulled-back (preimage 'mapping 'target)
        image-inclusion (subset V 'B mapped 'target)
        source-inclusion (subset U 'A 'source pulled-back)]
    {:name 'set/source-subset-preimage-of-image-subset
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['image-inclusion image-inclusion]]
      source-inclusion)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['image-inclusion image-inclusion]
       ['input 'A] ['source-member (function/app 'source 'input)]]
      (let [output (function/app 'mapping 'input)
            fiber (image-fiber 'mapping 'source output)
            image-member
            (function/app
             (function/const* 'proposition/witness [data-level])
             'A fiber 'input
             (function/app
              (function/const* 'proposition/conjoin [])
              (function/app 'source 'input)
              (function/equality target-data-level 'B output output)
              'source-member
              (function/app
               (function/const* 'equality/reflexive [target-data-level])
               'B output)))]
        (function/app 'image-inclusion output image-member)))}))

(def image-subset-equivalent-source-subset-preimage-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        mapped (image 'mapping 'source)
        pulled-back (preimage 'mapping 'target)
        image-inclusion (subset V 'B mapped 'target)
        source-inclusion (subset U 'A 'source pulled-back)]
    {:name 'set/image-subset-equivalent-source-subset-preimage
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]]
      (proposition/equivalence image-inclusion source-inclusion))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       image-inclusion source-inclusion
       (function/app
        (function/const*
         'set/source-subset-preimage-of-image-subset [U V])
        'A 'B 'mapping 'source 'target)
       (function/app
        (function/const*
         'set/image-subset-of-source-subset-preimage [U V])
        'A 'B 'mapping 'source 'target)))}))

(def theorem-specs
  [image-subset-of-source-subset-preimage-spec
   source-subset-preimage-of-image-subset-spec
   image-subset-equivalent-source-subset-preimage-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sets.image-certificates])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :set-image-preimage-adjunction theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.sets.image-preimage-adjunction))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
