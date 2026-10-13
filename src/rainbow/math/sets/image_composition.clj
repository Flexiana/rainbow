(ns rainbow.math.sets.image-composition
  "The image of a composite map is the nested image, by mutual inclusion."
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

(defn- image [source-level target-level source-element target-element
              mapping source]
  (function/app (function/const* 'set/image
                                 [source-level target-level])
                source-element target-element mapping source))

(defn- subset [level element small large]
  (function/app (function/const* 'set/subset [level])
                element small large))

(defn- composed [outer inner]
  (function/app
   (function/const* 'function/compose
                    [data-level middle-data-level target-data-level])
   'A 'B 'C outer inner))

(defn- identity-map []
  (function/app (function/const* 'function/identity [data-level]) 'A))

(def image-identity-subset-source-spec
  (let [set-a (set-of U 'A)
        identity-image
        (image U U 'A 'A (identity-map) 'source)]
    {:name 'set/image-identity-subset-source
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source set-a]]
      (subset U 'A identity-image 'source))
     :value
     (function/lam
      [['A type-u] ['source set-a]
       ['value 'A]
       ['image-member (function/app identity-image 'value)]]
      (let [fiber
            (function/lam
             [['input 'A]]
             (proposition/conjunction
              (function/app 'source 'input)
              (function/equality data-level 'A
                                 (function/app (identity-map) 'input)
                                 'value)))]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A fiber (function/app 'source 'value) 'image-member
         (function/lam
          [['input 'A] ['fiber-evidence (function/app fiber 'input)]]
          (let [source-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app 'source 'input)
                 (function/equality data-level 'A
                                    (function/app (identity-map) 'input)
                                    'value)
                 'fiber-evidence)
                same
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app 'source 'input)
                 (function/equality data-level 'A
                                    (function/app (identity-map) 'input)
                                    'value)
                 'fiber-evidence)]
            (function/app
             same
             (function/lam
              [['candidate 'A]] (function/app 'source 'candidate))
             source-member))))))}))

(def source-subset-image-identity-spec
  (let [set-a (set-of U 'A)
        identity-image
        (image U U 'A 'A (identity-map) 'source)]
    {:name 'set/source-subset-image-identity
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source set-a]]
      (subset U 'A 'source identity-image))
     :value
     (function/lam
      [['A type-u] ['source set-a]
       ['value 'A]
       ['source-member (function/app 'source 'value)]]
      (let [fiber
            (function/lam
             [['input 'A]]
             (proposition/conjunction
              (function/app 'source 'input)
              (function/equality data-level 'A
                                 (function/app (identity-map) 'input)
                                 'value)))]
        (function/app
         (function/const* 'proposition/witness [data-level])
         'A fiber 'value
         (function/app
          (function/const* 'proposition/conjoin [])
          (function/app 'source 'value)
          (function/equality data-level 'A
                             (function/app (identity-map) 'value) 'value)
          'source-member
          (function/app
           (function/const* 'equality/reflexive [data-level])
           'A 'value)))))}))

(def image-identity-equivalent-source-spec
  (let [set-a (set-of U 'A)
        identity-image
        (image U U 'A 'A (identity-map) 'source)
        forward (subset U 'A identity-image 'source)
        backward (subset U 'A 'source identity-image)]
    {:name 'set/image-identity-equivalent-source
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
        (function/const* 'set/image-identity-subset-source [U])
        'A 'source)
       (function/app
        (function/const* 'set/source-subset-image-identity [U])
        'A 'source)))}))

(def image-compose-subset-nested-image-spec
  (let [set-a (set-of U 'A)
        inner-image
        (image U V 'A 'B 'inner 'source)
        composed-image
        (image U W 'A 'C (composed 'outer 'inner) 'source)
        nested-image
        (image V W 'B 'C 'outer inner-image)]
    {:name 'set/image-compose-subset-nested-image
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a]]
      (subset W 'C composed-image nested-image))
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a]
       ['value 'C]
       ['composed-member (function/app composed-image 'value)]]
      (let [composed-fiber
            (function/lam
             [['input 'A]]
             (proposition/conjunction
              (function/app 'source 'input)
              (function/equality
               target-data-level 'C
               (function/app (composed 'outer 'inner) 'input) 'value)))]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A composed-fiber (function/app nested-image 'value)
         'composed-member
         (function/lam
          [['input 'A]
           ['composed-fiber-evidence
            (function/app composed-fiber 'input)]]
          (let [source-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app 'source 'input)
                 (function/equality
                  target-data-level 'C
                  (function/app (composed 'outer 'inner) 'input) 'value)
                 'composed-fiber-evidence)
                maps-value
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app 'source 'input)
                 (function/equality
                  target-data-level 'C
                  (function/app (composed 'outer 'inner) 'input) 'value)
                 'composed-fiber-evidence)
                middle-value (function/app 'inner 'input)
                inner-fiber
                (function/lam
                 [['candidate 'A]]
                 (proposition/conjunction
                  (function/app 'source 'candidate)
                  (function/equality
                   middle-data-level 'B
                   (function/app 'inner 'candidate) middle-value)))
                inner-member
                (function/app
                 (function/const* 'proposition/witness [data-level])
                 'A inner-fiber 'input
                 (function/app
                  (function/const* 'proposition/conjoin [])
                  (function/app 'source 'input)
                  (function/equality
                   middle-data-level 'B
                   (function/app 'inner 'input) middle-value)
                  source-member
                  (function/app
                   (function/const* 'equality/reflexive [middle-data-level])
                   'B middle-value)))
                outer-fiber
                (function/lam
                 [['middle 'B]]
                 (proposition/conjunction
                  (function/app inner-image 'middle)
                  (function/equality
                   target-data-level 'C
                   (function/app 'outer 'middle) 'value)))]
            (function/app
             (function/const* 'proposition/witness [middle-data-level])
             'B outer-fiber middle-value
             (function/app
              (function/const* 'proposition/conjoin [])
              (function/app inner-image middle-value)
              (function/equality
               target-data-level 'C
               (function/app 'outer middle-value) 'value)
              inner-member maps-value)))))))}))

(def nested-image-subset-image-compose-spec
  (let [set-a (set-of U 'A)
        inner-image
        (image U V 'A 'B 'inner 'source)
        composed-image
        (image U W 'A 'C (composed 'outer 'inner) 'source)
        nested-image
        (image V W 'B 'C 'outer inner-image)]
    {:name 'set/nested-image-subset-image-compose
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a]]
      (subset W 'C nested-image composed-image))
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a]
       ['value 'C]
       ['nested-member (function/app nested-image 'value)]]
      (let [outer-fiber
            (function/lam
             [['middle 'B]]
             (proposition/conjunction
              (function/app inner-image 'middle)
              (function/equality
               target-data-level 'C
               (function/app 'outer 'middle) 'value)))]
        (function/app
         (function/const* 'proposition/use-witness [middle-data-level])
         'B outer-fiber (function/app composed-image 'value)
         'nested-member
         (function/lam
          [['middle 'B]
           ['outer-fiber-evidence (function/app outer-fiber 'middle)]]
          (let [inner-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app inner-image 'middle)
                 (function/equality
                  target-data-level 'C
                  (function/app 'outer 'middle) 'value)
                 'outer-fiber-evidence)
                outer-maps-value
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app inner-image 'middle)
                 (function/equality
                  target-data-level 'C
                  (function/app 'outer 'middle) 'value)
                 'outer-fiber-evidence)
                inner-fiber
                (function/lam
                 [['input 'A]]
                 (proposition/conjunction
                  (function/app 'source 'input)
                  (function/equality
                   middle-data-level 'B
                   (function/app 'inner 'input) 'middle)))]
            (function/app
             (function/const* 'proposition/use-witness [data-level])
             'A inner-fiber (function/app composed-image 'value)
             inner-member
             (function/lam
              [['input 'A]
               ['inner-fiber-evidence
                (function/app inner-fiber 'input)]]
              (let [source-member
                    (function/app
                     (function/const* 'proposition/left [])
                     (function/app 'source 'input)
                     (function/equality
                      middle-data-level 'B
                      (function/app 'inner 'input) 'middle)
                     'inner-fiber-evidence)
                    inner-maps-middle
                    (function/app
                     (function/const* 'proposition/right [])
                     (function/app 'source 'input)
                     (function/equality
                      middle-data-level 'B
                      (function/app 'inner 'input) 'middle)
                     'inner-fiber-evidence)
                    composed-maps-outer-middle
                    (function/app
                     (function/const* 'equality/congruent-function
                                      [middle-data-level target-data-level])
                     'B 'C 'outer
                     (function/app 'inner 'input) 'middle
                     inner-maps-middle)
                    composed-maps-value
                    (function/app
                     (function/const* 'equality/transitive
                                      [target-data-level])
                     'C
                     (function/app (composed 'outer 'inner) 'input)
                     (function/app 'outer 'middle) 'value
                     composed-maps-outer-middle outer-maps-value)
                    composed-fiber
                    (function/lam
                     [['candidate 'A]]
                     (proposition/conjunction
                      (function/app 'source 'candidate)
                      (function/equality
                       target-data-level 'C
                       (function/app (composed 'outer 'inner) 'candidate)
                       'value)))]
                (function/app
                 (function/const* 'proposition/witness [data-level])
                 'A composed-fiber 'input
                 (function/app
                  (function/const* 'proposition/conjoin [])
                  (function/app 'source 'input)
                  (function/equality
                   target-data-level 'C
                   (function/app (composed 'outer 'inner) 'input) 'value)
                  source-member composed-maps-value))))))))))}))

(def image-compose-equivalent-nested-image-spec
  (let [set-a (set-of U 'A)
        inner-image
        (image U V 'A 'B 'inner 'source)
        composed-image
        (image U W 'A 'C (composed 'outer 'inner) 'source)
        nested-image
        (image V W 'B 'C 'outer inner-image)
        forward (subset W 'C composed-image nested-image)
        backward (subset W 'C nested-image composed-image)]
    {:name 'set/image-compose-equivalent-nested-image
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a]]
      (proposition/conjunction forward backward))
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a]]
      (function/app
       (function/const* 'proposition/conjoin [])
       forward backward
       (function/app
        (function/const* 'set/image-compose-subset-nested-image [U V W])
        'A 'B 'C 'inner 'outer 'source)
       (function/app
        (function/const* 'set/nested-image-subset-image-compose [U V W])
        'A 'B 'C 'inner 'outer 'source)))}))

(def theorem-specs
  [image-identity-subset-source-spec
   source-subset-image-identity-spec
   image-identity-equivalent-source-spec
   image-compose-subset-nested-image-spec
   nested-image-subset-image-compose-spec
   image-compose-equivalent-nested-image-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      finite-set/extend-environment
      (support/extend-with :set-image-composition theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
