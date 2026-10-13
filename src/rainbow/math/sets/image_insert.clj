(ns rainbow.math.sets.image-insert
  "Images commute constructively with inserting one source value."
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

(defn- image [mapping source]
  (function/app (function/const* 'set/image [U V])
                'A 'B mapping source))

(defn- insert [level element selected source]
  (function/app (function/const* 'set/insert [level])
                element selected source))

(defn- subset [level element small large]
  (function/app (function/const* 'set/subset [level])
                element small large))

(defn- image-fiber [mapping source value]
  (function/lam
   [['input 'A]]
   (proposition/conjunction
    (function/app source 'input)
    (function/equality target-data-level 'B
                       (function/app mapping 'input) value))))

(defn- image-witness [mapping source value input source-member maps-value]
  (let [fiber (image-fiber mapping source value)]
    (function/app
     (function/const* 'proposition/witness [data-level])
     'A fiber input
     (function/app
      (function/const* 'proposition/conjoin [])
      (function/app source input)
      (function/equality target-data-level 'B
                         (function/app mapping input) value)
      source-member maps-value))))

(def image-insert-subset-insert-image-spec
  (let [set-a (set-of U 'A)
        inserted-source (insert U 'A 'selected 'source)
        source-image (image 'mapping 'source)
        inserted-image
        (insert V 'B (function/app 'mapping 'selected) source-image)
        image-inserted (image 'mapping inserted-source)]
    {:name 'set/image-insert-subset-insert-image
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['selected 'A] ['source set-a]]
      (subset V 'B image-inserted inserted-image))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['selected 'A] ['source set-a]
       ['value 'B]
       ['image-member (function/app image-inserted 'value)]]
      (let [fiber (image-fiber 'mapping inserted-source 'value)]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A fiber (function/app inserted-image 'value) 'image-member
         (function/lam
          [['input 'A] ['fiber-evidence (function/app fiber 'input)]]
          (let [inserted-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app inserted-source 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'fiber-evidence)
                maps-value
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app inserted-source 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'fiber-evidence)]
            (function/app
             (function/const* 'proposition/use-disjunction [])
             (function/equality data-level 'A 'input 'selected)
             (function/app 'source 'input)
             (function/app inserted-image 'value) inserted-member
             (function/lam
              [['same-input
                (function/equality data-level 'A 'input 'selected)]]
              (let [same-mapping
                    (function/app
                     (function/const* 'equality/congruent-function
                                      [data-level target-data-level])
                     'A 'B 'mapping 'input 'selected 'same-input)
                    value-to-selected
                    (function/app
                    (function/const* 'equality/transitive
                                      [target-data-level])
                     'B 'value (function/app 'mapping 'input)
                     (function/app 'mapping 'selected)
                     (function/app
                      (function/const* 'equality/symmetric
                                       [target-data-level])
                      'B (function/app 'mapping 'input) 'value maps-value)
                     same-mapping)]
                (function/app
                 (function/const* 'proposition/left-disjunct [])
                 (function/equality target-data-level 'B
                                    'value
                                    (function/app 'mapping 'selected))
                 (function/app source-image 'value)
                 value-to-selected)))
             (function/lam
              [['source-member (function/app 'source 'input)]]
              (function/app
               (function/const* 'proposition/right-disjunct [])
               (function/equality target-data-level 'B
                                  'value (function/app 'mapping 'selected))
               (function/app source-image 'value)
               (image-witness 'mapping 'source 'value 'input
                              'source-member maps-value)))))))))}))

(def insert-image-subset-image-insert-spec
  (let [set-a (set-of U 'A)
        inserted-source (insert U 'A 'selected 'source)
        source-image (image 'mapping 'source)
        inserted-image
        (insert V 'B (function/app 'mapping 'selected) source-image)
        image-inserted (image 'mapping inserted-source)]
    {:name 'set/insert-image-subset-image-insert
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['selected 'A] ['source set-a]]
      (subset V 'B inserted-image image-inserted))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['selected 'A] ['source set-a]
       ['value 'B]
       ['inserted-member (function/app inserted-image 'value)]]
      (function/app
       (function/const* 'proposition/use-disjunction [])
       (function/equality target-data-level 'B
                          'value (function/app 'mapping 'selected))
       (function/app source-image 'value)
       (function/app image-inserted 'value) 'inserted-member
       (function/lam
        [['same-value
          (function/equality target-data-level 'B
                             'value (function/app 'mapping 'selected))]]
        (let [selected-member
              (function/app
               (function/const* 'proposition/left-disjunct [])
               (function/equality data-level 'A 'selected 'selected)
               (function/app 'source 'selected)
               (function/app
                (function/const* 'equality/reflexive [data-level])
                'A 'selected))
              mapping-to-value
              (function/app
               (function/const* 'equality/symmetric [target-data-level])
               'B 'value (function/app 'mapping 'selected) 'same-value)]
          (image-witness 'mapping inserted-source 'value 'selected
                         selected-member mapping-to-value)))
       (function/lam
        [['source-image-member (function/app source-image 'value)]]
        (let [fiber (image-fiber 'mapping 'source 'value)]
          (function/app
           (function/const* 'proposition/use-witness [data-level])
           'A fiber (function/app image-inserted 'value)
           'source-image-member
           (function/lam
            [['input 'A] ['fiber-evidence (function/app fiber 'input)]]
            (let [source-member
                  (function/app
                   (function/const* 'proposition/left [])
                   (function/app 'source 'input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'input) 'value)
                   'fiber-evidence)
                  maps-value
                  (function/app
                   (function/const* 'proposition/right [])
                   (function/app 'source 'input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'input) 'value)
                   'fiber-evidence)
                  inserted-source-member
                  (function/app
                   (function/const* 'proposition/right-disjunct [])
                   (function/equality data-level 'A 'input 'selected)
                   (function/app 'source 'input) source-member)]
              (image-witness 'mapping inserted-source 'value 'input
                             inserted-source-member maps-value))))))))}))

(def image-insert-equivalent-insert-image-spec
  (let [set-a (set-of U 'A)
        inserted-source (insert U 'A 'selected 'source)
        source-image (image 'mapping 'source)
        inserted-image
        (insert V 'B (function/app 'mapping 'selected) source-image)
        image-inserted (image 'mapping inserted-source)
        forward (subset V 'B image-inserted inserted-image)
        backward (subset V 'B inserted-image image-inserted)]
    {:name 'set/image-insert-equivalent-insert-image
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['selected 'A] ['source set-a]]
      (proposition/conjunction forward backward))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['selected 'A] ['source set-a]]
      (function/app
       (function/const* 'proposition/conjoin [])
       forward backward
       (function/app
        (function/const* 'set/image-insert-subset-insert-image [U V])
        'A 'B 'mapping 'selected 'source)
       (function/app
        (function/const* 'set/insert-image-subset-image-insert [U V])
        'A 'B 'mapping 'selected 'source)))}))

(def theorem-specs
  [image-insert-subset-insert-image-spec
   insert-image-subset-image-insert-spec
   image-insert-equivalent-insert-image-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      finite-set/extend-environment
      (support/extend-with :set-image-insert theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
