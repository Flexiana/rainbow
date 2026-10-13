(ns rainbow.math.sets.fiber-characterization
  "Image, surjection, and injection characterized by their source fibers."
  (:require [rainbow.math.finite.set-fiber :as fiber]
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

(defn- equality [level element left right]
  (function/equality level element left right))

(defn- fiber-within [mapping source target]
  (function/app (function/const* 'set/fiber-within [U V])
                'A 'B mapping source target))

(defn- image [mapping source]
  (function/app (function/const* 'set/image [U V])
                'A 'B mapping source))

(defn- nonempty [source]
  (function/app (function/const* 'set/nonempty [U]) 'A source))

(defn- subsingleton [source]
  (function/app (function/const* 'set/subsingleton [U]) 'A source))

(defn- injective-on [mapping source]
  (function/app (function/const* 'set/injective-on [U V])
                'A 'B mapping source))

(defn- surjective-on [mapping source target]
  (function/app (function/const* 'set/surjective-on [U V])
                'A 'B mapping source target))

(def fiber-nonempty-of-image-member-spec
  (let [fiber-set (fiber-within 'mapping 'source 'target)
        image-set (image 'mapping 'source)]
    {:name 'set/fiber-nonempty-of-image-member
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)] ['target 'B]
       ['image-member (function/app image-set 'target)]]
      (nonempty fiber-set))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)] ['target 'B]
       ['image-member (function/app image-set 'target)]]
      'image-member)}))

(def image-member-of-fiber-nonempty-spec
  (let [fiber-set (fiber-within 'mapping 'source 'target)
        image-set (image 'mapping 'source)]
    {:name 'set/image-member-of-fiber-nonempty
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)] ['target 'B]
       ['fiber-nonempty (nonempty fiber-set)]]
      (function/app image-set 'target))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)] ['target 'B]
       ['fiber-nonempty (nonempty fiber-set)]]
      'fiber-nonempty)}))

(def image-member-equivalent-fiber-nonempty-spec
  (let [fiber-set (fiber-within 'mapping 'source 'target)
        image-member (function/app (image 'mapping 'source) 'target)
        fiber-nonempty (nonempty fiber-set)]
    {:name 'set/image-member-equivalent-fiber-nonempty
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)] ['target 'B]]
      (proposition/equivalence image-member fiber-nonempty))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)] ['target 'B]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       image-member fiber-nonempty
       (function/app
        (function/const* 'set/fiber-nonempty-of-image-member [U V])
        'A 'B 'mapping 'source 'target)
       (function/app
        (function/const* 'set/image-member-of-fiber-nonempty [U V])
        'A 'B 'mapping 'source 'target)))}))

(def surjective-on-equivalent-nonempty-fibers-spec
  (let [set-b (set-of V 'B)
        onto (surjective-on 'mapping 'source 'target)
        all-fibers-nonempty
        (function/forall
         [['value 'B :implicit]
          ['target-member (function/app 'target 'value)]]
         (nonempty (fiber-within 'mapping 'source 'value)))]
    {:name 'set/surjective-on-equivalent-nonempty-fibers
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)] ['target set-b]]
      (proposition/equivalence onto all-fibers-nonempty))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)] ['target set-b]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       onto all-fibers-nonempty
       (function/lam [['onto-evidence onto]] 'onto-evidence)
       (function/lam
        [['fiber-evidence all-fibers-nonempty]] 'fiber-evidence)))}))

(def injective-on-equivalent-subsingleton-fibers-spec
  (let [injection (injective-on 'mapping 'source)
        all-fibers-subsingleton
        (function/forall
         [['target 'B]]
         (subsingleton (fiber-within 'mapping 'source 'target)))]
    {:name 'set/injective-on-equivalent-subsingleton-fibers
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]]
      (proposition/equivalence injection all-fibers-subsingleton))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       injection all-fibers-subsingleton
       (function/lam
        [['injection-evidence injection]
         ['target 'B]
         ['left 'A :implicit]
         ['left-fiber
          (function/app (fiber-within 'mapping 'source 'target) 'left)]
         ['right 'A :implicit]
         ['right-fiber
          (function/app (fiber-within 'mapping 'source 'target) 'right)]]
        (function/app
         'injection-evidence
         'left
         (function/app
          (function/const* 'set/fiber-within-member-source [U V])
          'A 'B 'mapping 'source 'target 'left 'left-fiber)
         'right
         (function/app
          (function/const* 'set/fiber-within-member-source [U V])
          'A 'B 'mapping 'source 'target 'right 'right-fiber)
         (function/app
          (function/const* 'equality/transitive [target-data-level])
          'B (function/app 'mapping 'left) 'target
          (function/app 'mapping 'right)
          (function/app
           (function/const* 'set/fiber-within-mapping-equals [U V])
           'A 'B 'mapping 'source 'target 'left 'left-fiber)
          (function/app
           (function/const* 'equality/symmetric [target-data-level])
           'B (function/app 'mapping 'right) 'target
           (function/app
            (function/const* 'set/fiber-within-mapping-equals [U V])
            'A 'B 'mapping 'source 'target 'right 'right-fiber)))))
       (function/lam
        [['fiber-evidence all-fibers-subsingleton]
         ['left 'A :implicit]
         ['left-member (function/app 'source 'left)]
         ['right 'A :implicit]
         ['right-member (function/app 'source 'right)]
         ['same-image
          (equality target-data-level 'B
                    (function/app 'mapping 'left)
                    (function/app 'mapping 'right))]]
        (let [target (function/app 'mapping 'right)
              target-fiber (fiber-within 'mapping 'source target)]
          (function/app
           (function/app 'fiber-evidence target)
           'left
           (function/app
            (function/const* 'proposition/conjoin [])
            (function/app 'source 'left)
            (equality target-data-level 'B
                      (function/app 'mapping 'left) target)
            'left-member 'same-image)
           'right
           (function/app
            (function/const* 'proposition/conjoin [])
            (function/app 'source 'right)
            (equality target-data-level 'B
                      (function/app 'mapping 'right) target)
            'right-member
            (function/app
             (function/const* 'equality/reflexive [target-data-level])
             'B target)))))))}))

(def theorem-specs
  [fiber-nonempty-of-image-member-spec
   image-member-of-fiber-nonempty-spec
   image-member-equivalent-fiber-nonempty-spec
   surjective-on-equivalent-nonempty-fibers-spec
   injective-on-equivalent-subsingleton-fibers-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      fiber/extend-environment
      (support/extend-with :set-fiber-characterization theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
