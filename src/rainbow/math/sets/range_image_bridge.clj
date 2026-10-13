(ns rainbow.math.sets.range-image-bridge
  "Bridge global function ranges to images of universal source sets."
  (:require [rainbow.math.finite.set :as finite-set]
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

(defn- universal [level element]
  (function/app (function/const* 'set/universal [level]) element))

(defn- range-set [mapping]
  (function/app (function/const* 'set/range [U V])
                'A 'B mapping))

(defn- image-universal [mapping]
  (function/app (function/const* 'set/image [U V])
                'A 'B mapping (universal U 'A)))

(defn- subset [small large]
  (function/app (function/const* 'set/subset [V])
                'B small large))

(def range-subset-image-universal-spec
  (let [range (range-set 'mapping)
        image (image-universal 'mapping)]
    {:name 'set/range-subset-image-universal
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]]
      (subset range image))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['value 'B] ['range-member (function/app range 'value)]]
      (let [range-fiber
            (function/lam
             [['input 'A]]
             (function/equality target-data-level 'B
                                (function/app 'mapping 'input) 'value))
            image-fiber
            (function/lam
             [['input 'A]]
             (proposition/conjunction
              (function/app (universal U 'A) 'input)
              (function/equality target-data-level 'B
                                 (function/app 'mapping 'input) 'value)))]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A range-fiber (function/app image 'value) 'range-member
         (function/lam
          [['input 'A]
           ['maps-value (function/app range-fiber 'input)]]
          (function/app
           (function/const* 'proposition/witness [data-level])
           'A image-fiber 'input
           (function/app
            (function/const* 'proposition/conjoin [])
            (function/app (universal U 'A) 'input)
            (function/equality target-data-level 'B
                               (function/app 'mapping 'input) 'value)
            (function/const* 'proposition/trivial [])
            'maps-value))))))}))

(def image-universal-subset-range-spec
  (let [range (range-set 'mapping)
        image (image-universal 'mapping)]
    {:name 'set/image-universal-subset-range
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]]
      (subset image range))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['value 'B] ['image-member (function/app image 'value)]]
      (let [image-fiber
            (function/lam
             [['input 'A]]
             (proposition/conjunction
              (function/app (universal U 'A) 'input)
              (function/equality target-data-level 'B
                                 (function/app 'mapping 'input) 'value)))
            range-fiber
            (function/lam
             [['input 'A]]
             (function/equality target-data-level 'B
                                (function/app 'mapping 'input) 'value))]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A image-fiber (function/app range 'value) 'image-member
         (function/lam
          [['input 'A]
           ['image-fiber-evidence (function/app image-fiber 'input)]]
          (function/app
           (function/const* 'proposition/witness [data-level])
           'A range-fiber 'input
           (function/app
            (function/const* 'proposition/right [])
            (function/app (universal U 'A) 'input)
            (function/equality target-data-level 'B
                               (function/app 'mapping 'input) 'value)
            'image-fiber-evidence))))))}))

(def range-equivalent-image-universal-spec
  (let [range (range-set 'mapping)
        image (image-universal 'mapping)
        forward (subset range image)
        backward (subset image range)]
    {:name 'set/range-equivalent-image-universal
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]]
      (proposition/conjunction forward backward))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]]
      (function/app
       (function/const* 'proposition/conjoin [])
       forward backward
       (function/app
        (function/const* 'set/range-subset-image-universal [U V])
        'A 'B 'mapping)
       (function/app
        (function/const* 'set/image-universal-subset-range [U V])
        'A 'B 'mapping)))}))

(def surjective-equivalent-universal-subset-range-spec
  (let [range (range-set 'mapping)
        universal-b (universal V 'B)
        surjective
        (function/surjective data-level target-data-level
                              'A 'B 'mapping)
        covers-range (subset universal-b range)]
    {:name 'function/surjective-equivalent-universal-subset-range
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]]
      (proposition/equivalence surjective covers-range))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       surjective covers-range
       (function/lam
        [['surjection-evidence surjective]
         ['value 'B]
         ['universal-member (function/app universal-b 'value)]]
        (function/app 'surjection-evidence 'value))
       (function/lam
        [['range-cover covers-range]
         ['value 'B]]
        (function/app
         'range-cover 'value
         (function/const* 'proposition/trivial [])))))}))

(def theorem-specs
  [range-subset-image-universal-spec
   image-universal-subset-range-spec
   range-equivalent-image-universal-spec
   surjective-equivalent-universal-subset-range-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      finite-set/extend-environment
      (support/extend-with :set-range-image-bridge theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
