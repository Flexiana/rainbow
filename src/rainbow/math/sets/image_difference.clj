(ns rainbow.math.sets.image-difference
  "Images preserve set difference exactly when witnesses cannot collide."
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

(defn- difference [level element left right]
  (function/app (function/const* 'set/difference [level])
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

(def image-difference-subset-difference-images-of-injective-spec
  (let [set-a (set-of U 'A)
        source-union (union U 'A 'left 'right)
        source-difference (difference U 'A 'left 'right)
        left-image (image 'mapping 'left)
        right-image (image 'mapping 'right)
        difference-images (difference V 'B left-image right-image)
        difference-image (image 'mapping source-difference)
        injection (injective-on 'mapping source-union)]
    {:name 'set/image-difference-subset-difference-images-of-injective
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['injection-evidence injection]]
      (subset V 'B difference-image difference-images))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['injection-evidence injection]
       ['value 'B]
       ['difference-member (function/app difference-image 'value)]]
      (let [difference-fiber
            (image-fiber 'mapping source-difference 'value)]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A difference-fiber (function/app difference-images 'value)
         'difference-member
         (function/lam
          [['left-input 'A]
           ['difference-fiber-evidence
            (function/app difference-fiber 'left-input)]]
          (let [source-difference-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app source-difference 'left-input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'left-input)
                                    'value)
                 'difference-fiber-evidence)
                left-maps-value
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app source-difference 'left-input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'left-input)
                                    'value)
                 'difference-fiber-evidence)
                left-member
                (function/app (function/const* 'proposition/left [])
                              (function/app 'left 'left-input)
                              (proposition/negation
                               (function/app 'right 'left-input))
                              source-difference-member)
                not-right
                (function/app (function/const* 'proposition/right [])
                              (function/app 'left 'left-input)
                              (proposition/negation
                               (function/app 'right 'left-input))
                              source-difference-member)
                left-image-member
                (image-witness 'mapping 'left 'value 'left-input
                               left-member left-maps-value)
                not-right-image
                (function/lam
                 [['right-image-member (function/app right-image 'value)]]
                 (let [right-fiber (image-fiber 'mapping 'right 'value)]
                   (function/app
                    (function/const* 'proposition/use-witness [data-level])
                    'A right-fiber (proposition/falsity)
                    'right-image-member
                    (function/lam
                     [['right-input 'A]
                      ['right-fiber-evidence
                       (function/app right-fiber 'right-input)]]
                     (let [right-member
                           (function/app
                            (function/const* 'proposition/left [])
                            (function/app 'right 'right-input)
                            (function/equality
                             target-data-level 'B
                             (function/app 'mapping 'right-input) 'value)
                            'right-fiber-evidence)
                           right-maps-value
                           (function/app
                            (function/const* 'proposition/right [])
                            (function/app 'right 'right-input)
                            (function/equality
                             target-data-level 'B
                             (function/app 'mapping 'right-input) 'value)
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
                            (function/const* 'equality/transitive
                                             [target-data-level])
                            'B (function/app 'mapping 'left-input) 'value
                            (function/app 'mapping 'right-input)
                            left-maps-value
                            (function/app
                             (function/const* 'equality/symmetric
                                              [target-data-level])
                             'B (function/app 'mapping 'right-input) 'value
                             right-maps-value))
                           same-input
                           (function/app
                            'injection-evidence
                            'left-input left-union-member
                            'right-input right-union-member same-image)
                           right-member-left
                           (function/app
                            (function/app
                             (function/const* 'equality/symmetric [data-level])
                             'A 'left-input 'right-input same-input)
                            (function/lam
                             [['candidate 'A]]
                             (function/app 'right 'candidate))
                            right-member)]
                       (function/app not-right right-member-left))))))]
            (function/app
             (function/const* 'proposition/conjoin [])
             (function/app left-image 'value)
             (proposition/negation (function/app right-image 'value))
             left-image-member not-right-image))))))}))

(def difference-images-subset-image-difference-spec
  (let [set-a (set-of U 'A)
        source-difference (difference U 'A 'left 'right)
        left-image (image 'mapping 'left)
        right-image (image 'mapping 'right)
        difference-images (difference V 'B left-image right-image)
        difference-image (image 'mapping source-difference)]
    {:name 'set/difference-images-subset-image-difference
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]]
      (subset V 'B difference-images difference-image))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['left set-a] ['right set-a]
       ['value 'B]
       ['difference-member (function/app difference-images 'value)]]
      (let [left-image-member
            (function/app
             (function/const* 'proposition/left [])
             (function/app left-image 'value)
             (proposition/negation (function/app right-image 'value))
             'difference-member)
            not-right-image
            (function/app
             (function/const* 'proposition/right [])
             (function/app left-image 'value)
             (proposition/negation (function/app right-image 'value))
             'difference-member)
            left-fiber (image-fiber 'mapping 'left 'value)]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A left-fiber (function/app difference-image 'value)
         left-image-member
         (function/lam
          [['input 'A]
           ['left-fiber-evidence (function/app left-fiber 'input)]]
          (let [left-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app 'left 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'left-fiber-evidence)
                maps-value
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app 'left 'input)
                 (function/equality target-data-level 'B
                                    (function/app 'mapping 'input) 'value)
                 'left-fiber-evidence)
                not-right
                (function/lam
                 [['right-member (function/app 'right 'input)]]
                 (function/app
                  not-right-image
                  (image-witness 'mapping 'right 'value 'input
                                 'right-member maps-value)))
                source-difference-member
                (function/app
                 (function/const* 'proposition/conjoin [])
                 (function/app 'left 'input)
                 (proposition/negation (function/app 'right 'input))
                 left-member not-right)]
            (image-witness 'mapping source-difference 'value 'input
                           source-difference-member maps-value))))))}))

(def image-difference-equivalent-difference-images-of-injective-spec
  (let [set-a (set-of U 'A)
        source-union (union U 'A 'left 'right)
        source-difference (difference U 'A 'left 'right)
        difference-images
        (difference V 'B (image 'mapping 'left) (image 'mapping 'right))
        difference-image (image 'mapping source-difference)
        injection (injective-on 'mapping source-union)
        forward (subset V 'B difference-image difference-images)
        backward (subset V 'B difference-images difference-image)]
    {:name 'set/image-difference-equivalent-difference-images-of-injective
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
         'set/image-difference-subset-difference-images-of-injective [U V])
        'A 'B 'mapping 'left 'right 'injection-evidence)
       (function/app
        (function/const* 'set/difference-images-subset-image-difference [U V])
        'A 'B 'mapping 'left 'right)))}))

(def theorem-specs
  [image-difference-subset-difference-images-of-injective-spec
   difference-images-subset-image-difference-spec
   image-difference-equivalent-difference-images-of-injective-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.set])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :set-image-difference theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.sets.image-difference))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
