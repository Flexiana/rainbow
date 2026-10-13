(ns rainbow.math.sets.image-lattice
  "Images preserve unions, and preserve intersections under injectivity."
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

(defn- image [mapping source]
  (function/app (function/const* 'set/image [U V])
                'A 'B mapping source))

(defn- union [level element left right]
  (function/app (function/const* 'set/union [level])
                element left right))

(defn- intersection [level element left right]
  (function/app (function/const* 'set/intersection [level])
                element left right))

(defn- subset [level element small large]
  (function/app (function/const* 'set/subset [level])
                element small large))

(defn- injective-on [mapping source]
  (function/app (function/const* 'set/injective-on [U V])
                'A 'B mapping source))

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

(def image-union-subset-union-images-spec
  (let [set-a (set-of U 'A)
        source-union (union U 'A 'left 'right)
        left-image (image 'mapping 'left)
        right-image (image 'mapping 'right)
        union-images (union V 'B left-image right-image)
        joined-image (image 'mapping source-union)]
    {:name 'set/image-union-subset-union-images
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]]
      (subset V 'B joined-image union-images))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['value 'B]
       ['joined-member (function/app joined-image 'value)]]
      (let [fiber (image-fiber 'mapping source-union 'value)]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A fiber (function/app union-images 'value) 'joined-member
         (function/lam
          [['input 'A] ['fiber-evidence (function/app fiber 'input)]]
          (let [source-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app source-union 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'fiber-evidence)
                maps-value
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app source-union 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'fiber-evidence)]
            (function/app
             (function/const* 'proposition/use-disjunction [])
             (function/app 'left 'input) (function/app 'right 'input)
             (function/app union-images 'value) source-member
             (function/lam
              [['left-member (function/app 'left 'input)]]
              (function/app
               (function/const* 'proposition/left-disjunct [])
               (function/app left-image 'value)
               (function/app right-image 'value)
               (image-witness 'mapping 'left 'value 'input
                              'left-member maps-value)))
             (function/lam
              [['right-member (function/app 'right 'input)]]
              (function/app
               (function/const* 'proposition/right-disjunct [])
               (function/app left-image 'value)
               (function/app right-image 'value)
               (image-witness 'mapping 'right 'value 'input
                              'right-member maps-value)))))))))}))

(def union-images-subset-image-union-spec
  (let [set-a (set-of U 'A)
        source-union (union U 'A 'left 'right)
        left-image (image 'mapping 'left)
        right-image (image 'mapping 'right)
        union-images (union V 'B left-image right-image)
        joined-image (image 'mapping source-union)]
    {:name 'set/union-images-subset-image-union
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]]
      (subset V 'B union-images joined-image))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['value 'B]
       ['union-member (function/app union-images 'value)]]
      (function/app
       (function/const* 'proposition/use-disjunction [])
       (function/app left-image 'value)
       (function/app right-image 'value)
       (function/app joined-image 'value) 'union-member
       (function/lam
        [['left-image-member (function/app left-image 'value)]]
        (let [fiber (image-fiber 'mapping 'left 'value)]
          (function/app
           (function/const* 'proposition/use-witness [data-level])
           'A fiber (function/app joined-image 'value) 'left-image-member
           (function/lam
            [['input 'A] ['fiber-evidence (function/app fiber 'input)]]
            (let [left-member
                  (function/app
                   (function/const* 'proposition/left [])
                   (function/app 'left 'input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'input) 'value)
                   'fiber-evidence)
                  maps-value
                  (function/app
                   (function/const* 'proposition/right [])
                   (function/app 'left 'input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'input) 'value)
                   'fiber-evidence)
                  union-member
                  (function/app
                   (function/const* 'proposition/left-disjunct [])
                   (function/app 'left 'input) (function/app 'right 'input)
                   left-member)]
              (image-witness 'mapping source-union 'value 'input
                             union-member maps-value))))))
       (function/lam
        [['right-image-member (function/app right-image 'value)]]
        (let [fiber (image-fiber 'mapping 'right 'value)]
          (function/app
           (function/const* 'proposition/use-witness [data-level])
           'A fiber (function/app joined-image 'value) 'right-image-member
           (function/lam
            [['input 'A] ['fiber-evidence (function/app fiber 'input)]]
            (let [right-member
                  (function/app
                   (function/const* 'proposition/left [])
                   (function/app 'right 'input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'input) 'value)
                   'fiber-evidence)
                  maps-value
                  (function/app
                   (function/const* 'proposition/right [])
                   (function/app 'right 'input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'input) 'value)
                   'fiber-evidence)
                  union-member
                  (function/app
                   (function/const* 'proposition/right-disjunct [])
                   (function/app 'left 'input) (function/app 'right 'input)
                   right-member)]
              (image-witness 'mapping source-union 'value 'input
                             union-member maps-value))))))))}))

(def image-union-equivalent-union-images-spec
  (let [set-a (set-of U 'A)
        source-union (union U 'A 'left 'right)
        union-images
        (union V 'B (image 'mapping 'left) (image 'mapping 'right))
        joined-image (image 'mapping source-union)
        forward (subset V 'B joined-image union-images)
        backward (subset V 'B union-images joined-image)]
    {:name 'set/image-union-equivalent-union-images
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]]
      (proposition/conjunction forward backward))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]]
      (function/app
       (function/const* 'proposition/conjoin [])
       forward backward
       (function/app
        (function/const* 'set/image-union-subset-union-images [U V])
        'A 'B 'mapping 'left 'right)
       (function/app
        (function/const* 'set/union-images-subset-image-union [U V])
        'A 'B 'mapping 'left 'right)))}))

(def image-intersection-subset-intersection-images-spec
  (let [set-a (set-of U 'A)
        source-intersection (intersection U 'A 'left 'right)
        left-image (image 'mapping 'left)
        right-image (image 'mapping 'right)
        intersection-images (intersection V 'B left-image right-image)
        shared-image (image 'mapping source-intersection)]
    {:name 'set/image-intersection-subset-intersection-images
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]]
      (subset V 'B shared-image intersection-images))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['value 'B]
       ['shared-member (function/app shared-image 'value)]]
      (let [fiber (image-fiber 'mapping source-intersection 'value)]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A fiber (function/app intersection-images 'value) 'shared-member
         (function/lam
          [['input 'A] ['fiber-evidence (function/app fiber 'input)]]
          (let [intersection-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app source-intersection 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'fiber-evidence)
                maps-value
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app source-intersection 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'fiber-evidence)
                left-member
                (function/app (function/const* 'proposition/left [])
                              (function/app 'left 'input)
                              (function/app 'right 'input)
                              intersection-member)
                right-member
                (function/app (function/const* 'proposition/right [])
                              (function/app 'left 'input)
                              (function/app 'right 'input)
                              intersection-member)]
            (function/app
             (function/const* 'proposition/conjoin [])
             (function/app left-image 'value)
             (function/app right-image 'value)
             (image-witness 'mapping 'left 'value 'input
                            left-member maps-value)
             (image-witness 'mapping 'right 'value 'input
                            right-member maps-value)))))))}))

(def intersection-images-subset-image-intersection-of-injective-spec
  (let [set-a (set-of U 'A)
        source-union (union U 'A 'left 'right)
        source-intersection (intersection U 'A 'left 'right)
        left-image (image 'mapping 'left)
        right-image (image 'mapping 'right)
        intersection-images (intersection V 'B left-image right-image)
        shared-image (image 'mapping source-intersection)
        injection (injective-on 'mapping source-union)]
    {:name 'set/intersection-images-subset-image-intersection-of-injective
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['injection-evidence injection]]
      (subset V 'B intersection-images shared-image))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['injection-evidence injection]
       ['value 'B]
       ['intersection-member (function/app intersection-images 'value)]]
      (let [left-image-member
            (function/app (function/const* 'proposition/left [])
                          (function/app left-image 'value)
                          (function/app right-image 'value)
                          'intersection-member)
            right-image-member
            (function/app (function/const* 'proposition/right [])
                          (function/app left-image 'value)
                          (function/app right-image 'value)
                          'intersection-member)
            left-fiber (image-fiber 'mapping 'left 'value)
            right-fiber (image-fiber 'mapping 'right 'value)]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A left-fiber (function/app shared-image 'value) left-image-member
         (function/lam
          [['left-input 'A]
           ['left-fiber-evidence (function/app left-fiber 'left-input)]]
          (function/app
           (function/const* 'proposition/use-witness [data-level])
           'A right-fiber (function/app shared-image 'value)
           right-image-member
           (function/lam
            [['right-input 'A]
             ['right-fiber-evidence
              (function/app right-fiber 'right-input)]]
            (let [left-member
                  (function/app
                   (function/const* 'proposition/left [])
                   (function/app 'left 'left-input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'left-input)
                                      'value)
                   'left-fiber-evidence)
                  left-maps-value
                  (function/app
                   (function/const* 'proposition/right [])
                   (function/app 'left 'left-input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'left-input)
                                      'value)
                   'left-fiber-evidence)
                  right-member
                  (function/app
                   (function/const* 'proposition/left [])
                   (function/app 'right 'right-input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'right-input)
                                      'value)
                   'right-fiber-evidence)
                  right-maps-value
                  (function/app
                   (function/const* 'proposition/right [])
                   (function/app 'right 'right-input)
                   (function/equality target-data-level 'B
                                      (function/app 'mapping 'right-input)
                                      'value)
                   'right-fiber-evidence)
                  left-union-member
                  (function/app
                   (function/const* 'proposition/left-disjunct [])
                   (function/app 'left 'left-input)
                   (function/app 'right 'left-input) left-member)
                  right-union-member
                  (function/app
                   (function/const* 'proposition/right-disjunct [])
                   (function/app 'left 'right-input)
                   (function/app 'right 'right-input) right-member)
                  same-image
                  (function/app
                   (function/const* 'equality/transitive [target-data-level])
                   'B (function/app 'mapping 'left-input) 'value
                   (function/app 'mapping 'right-input)
                   left-maps-value
                   (function/app
                    (function/const* 'equality/symmetric [target-data-level])
                    'B (function/app 'mapping 'right-input) 'value
                    right-maps-value))
                  same-input
                  (function/app 'injection-evidence
                                'left-input left-union-member
                                'right-input right-union-member same-image)
                  right-member-left
                  (function/app
                   (function/app
                    (function/const* 'equality/symmetric [data-level])
                    'A 'left-input 'right-input same-input)
                   (function/lam
                    [['candidate 'A]] (function/app 'right 'candidate))
                   right-member)
                  shared-source-member
                  (function/app
                   (function/const* 'proposition/conjoin [])
                   (function/app 'left 'left-input)
                   (function/app 'right 'left-input)
                   left-member right-member-left)]
              (image-witness 'mapping source-intersection 'value
                             'left-input shared-source-member
                             left-maps-value))))))))}))

(def image-intersection-equivalent-intersection-images-of-injective-spec
  (let [set-a (set-of U 'A)
        source-union (union U 'A 'left 'right)
        source-intersection (intersection U 'A 'left 'right)
        intersection-images
        (intersection V 'B (image 'mapping 'left) (image 'mapping 'right))
        shared-image (image 'mapping source-intersection)
        injection (injective-on 'mapping source-union)
        forward (subset V 'B shared-image intersection-images)
        backward (subset V 'B intersection-images shared-image)]
    {:name 'set/image-intersection-equivalent-intersection-images-of-injective
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['injection-evidence injection]]
      (proposition/conjunction forward backward))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['injection-evidence injection]]
      (function/app
       (function/const* 'proposition/conjoin [])
       forward backward
       (function/app
        (function/const*
         'set/image-intersection-subset-intersection-images [U V])
        'A 'B 'mapping 'left 'right)
       (function/app
        (function/const*
         'set/intersection-images-subset-image-intersection-of-injective
         [U V])
        'A 'B 'mapping 'left 'right 'injection-evidence)))}))

(def theorem-specs
  [image-union-subset-union-images-spec
   union-images-subset-image-union-spec
   image-union-equivalent-union-images-spec
   image-intersection-subset-intersection-images-spec
   intersection-images-subset-image-intersection-of-injective-spec
   image-intersection-equivalent-intersection-images-of-injective-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.set])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :set-image-lattice theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.sets.image-lattice))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
