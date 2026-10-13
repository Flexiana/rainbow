(ns rainbow.math.finite.set-fiber-decomposition
  "A finite source is the union of its fibers over its finite image."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.set-fiber :as fiber]
            [rainbow.math.finite.set-indexed-union :as indexed-union]
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

(defn- equality [element left right]
  (function/equality target-data-level element left right))

(defn- subset [element small large]
  (function/app (function/const* 'set/subset [U])
                element small large))

(defn- finite [level element source]
  (function/app (function/const* 'set/finite [level]) element source))

(defn- image [source-element target-element mapping source]
  (function/app (function/const* 'set/image [U V])
                source-element target-element mapping source))

(defn- fiber-within [source-element target-element mapping source target]
  (function/app (function/const* 'set/fiber-within [U V])
                source-element target-element mapping source target))

(defn- restricted-indexed-union [element index indices family]
  (function/app (function/const* 'set/restricted-indexed-union [U V])
                element index indices family))

(defn- fiber-family [source-element target-element mapping source]
  (function/lam
   [['target target-element]]
   (fiber-within source-element target-element mapping source 'target)))

(defn- image-fiber-union [source-element target-element mapping source]
  (let [mapped (image source-element target-element mapping source)
        family (fiber-family source-element target-element mapping source)]
    (restricted-indexed-union source-element target-element mapped family)))

(def source-subset-image-fiber-union-spec
  (let [mapped (image 'A 'B 'mapping 'source)
        family (fiber-family 'A 'B 'mapping 'source)
        joined (image-fiber-union 'A 'B 'mapping 'source)]
    {:name 'set/source-subset-image-fiber-union
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]]
      (subset 'A 'source joined))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['value 'A]
       ['source-member (function/app 'source 'value)]]
      (let [target (function/app 'mapping 'value)
            reflexive
            (function/app
             (function/const* 'equality/reflexive [target-data-level])
             'B target)
            image-member
            (function/app
             (function/const* 'proposition/witness [data-level])
             'A
             (function/lam
              [['input 'A]]
              (proposition/conjunction
               (function/app 'source 'input)
               (equality 'B (function/app 'mapping 'input) target)))
             'value
             (function/app
              (function/const* 'proposition/conjoin [])
              (function/app 'source 'value)
              (equality 'B target target)
              'source-member reflexive))
            fiber-member
            (function/app
             (function/const* 'proposition/conjoin [])
             (function/app 'source 'value)
             (equality 'B target target)
             'source-member reflexive)]
        (function/app
         (function/const* 'set/restricted-indexed-union-member [U V])
         'A 'B mapped family
         target image-member
         'value fiber-member)))}))

(def image-fiber-union-subset-source-spec
  (let [mapped (image 'A 'B 'mapping 'source)
        family (fiber-family 'A 'B 'mapping 'source)
        joined (image-fiber-union 'A 'B 'mapping 'source)]
    {:name 'set/image-fiber-union-subset-source
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]]
      (subset 'A joined 'source))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['value 'A]
       ['member (function/app joined 'value)]]
      (function/app
       (function/const* 'proposition/use-witness [target-data-level])
       'B
       (function/lam
        [['target 'B]]
        (proposition/conjunction
         (function/app mapped 'target)
         (function/app family 'target 'value)))
       (function/app 'source 'value)
       'member
       (function/lam
        [['target 'B]
         ['both
          (proposition/conjunction
           (function/app mapped 'target)
           (function/app family 'target 'value))]]
        (function/app
         (function/const* 'set/fiber-within-member-source [U V])
         'A 'B 'mapping 'source 'target 'value
         (function/app
          (function/const* 'proposition/right [])
          (function/app mapped 'target)
          (function/app family 'target 'value)
          'both)))))}))

(def image-fiber-union-decomposition-spec
  (let [joined (image-fiber-union 'A 'B 'mapping 'source)
        forward (subset 'A 'source joined)
        backward (subset 'A joined 'source)]
    {:name 'set/image-fiber-union-decomposition
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]]
      (proposition/conjunction forward backward))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]]
      (function/app
       (function/const* 'proposition/conjoin [])
       forward backward
       (function/app
        (function/const* 'set/source-subset-image-fiber-union [U V])
        'A 'B 'mapping 'source)
       (function/app
        (function/const* 'set/image-fiber-union-subset-source [U V])
        'A 'B 'mapping 'source)))}))

(def finite-image-fiber-union-spec
  (let [mapped (image 'A 'B 'mapping 'source)
        family (fiber-family 'A 'B 'mapping 'source)
        joined (image-fiber-union 'A 'B 'mapping 'source)]
    {:name 'set/finite-image-fiber-union
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['source-finite (finite U 'A 'source)]]
      (finite U 'A joined))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['source-finite (finite U 'A 'source)]]
      (function/app
       (function/const* 'set/finite-restricted-indexed-union [U V])
       'A 'B mapped family
       (function/app
        (function/const* 'set/finite-image-preserved [U V])
        'A 'B 'source 'mapping 'source-finite)
       (function/lam
        [['target 'B]]
        (function/app
         (function/const* 'set/finite-fiber-within [U V])
         'A 'B 'mapping 'source 'target 'source-finite))))}))

(def definition-specs [])

(def theorem-specs
  [source-subset-image-fiber-union-spec
   image-fiber-union-subset-source-spec
   image-fiber-union-decomposition-spec
   finite-image-fiber-union-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.set-fiber rainbow.math.finite.set-indexed-union])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-set-fiber-decomposition theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.set-fiber-decomposition))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
