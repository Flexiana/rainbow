(ns rainbow.math.sets.map-composition
  "Constructive set-map properties preserved by function composition."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.set :as finite-set]
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

(defn- compose [outer inner]
  (function/app
   (function/const* 'function/compose
                    [data-level middle-data-level target-data-level])
   'A 'B 'C outer inner))

(defn- identity-map []
  (function/app (function/const* 'function/identity [data-level]) 'A))

(defn- maps-to [source-level target-level source-element target-element
                 mapping source target]
  (function/app (function/const* 'set/maps-to
                                 [source-level target-level])
                source-element target-element mapping source target))

(defn- injective-on [source-level target-level source-element target-element
                     mapping source]
  (function/app (function/const* 'set/injective-on
                                 [source-level target-level])
                source-element target-element mapping source))

(defn- surjective-on [source-level target-level source-element target-element
                      mapping source target]
  (function/app (function/const* 'set/surjective-on
                                 [source-level target-level])
                source-element target-element mapping source target))

(defn- bijective-on [source-level target-level source-element target-element
                     mapping source target]
  (function/app (function/const* 'set/bijective-on
                                 [source-level target-level])
                source-element target-element mapping source target))

(def maps-to-identity-spec
  (let [set-a (set-of U 'A)
        identity (identity-map)
        target (maps-to U U 'A 'A identity 'source 'source)]
    {:name 'set/maps-to-identity
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source set-a]] target)
     :value
     (function/lam
      [['A type-u] ['source set-a]
       ['value 'A :implicit]
       ['source-member (function/app 'source 'value)]]
      'source-member)}))

(def injective-on-identity-spec
  (let [set-a (set-of U 'A)
        identity (identity-map)
        target (injective-on U U 'A 'A identity 'source)]
    {:name 'set/injective-on-identity
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source set-a]] target)
     :value
     (function/lam
      [['A type-u] ['source set-a]
       ['left 'A :implicit]
       ['left-member (function/app 'source 'left)]
       ['right 'A :implicit]
       ['right-member (function/app 'source 'right)]
       ['same-image
        (function/equality data-level 'A
                           (function/app identity 'left)
                           (function/app identity 'right))]]
      'same-image)}))

(def surjective-on-identity-spec
  (let [set-a (set-of U 'A)
        identity (identity-map)
        target (surjective-on U U 'A 'A identity 'source 'source)]
    {:name 'set/surjective-on-identity
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source set-a]] target)
     :value
     (function/lam
      [['A type-u] ['source set-a]
       ['value 'A :implicit]
       ['source-member (function/app 'source 'value)]]
      (let [fiber
            (function/lam
             [['candidate 'A]]
             (proposition/conjunction
              (function/app 'source 'candidate)
              (function/equality data-level 'A
                                 (function/app identity 'candidate)
                                 'value)))]
        (function/app
         (function/const* 'proposition/witness [data-level])
         'A fiber 'value
         (function/app
          (function/const* 'proposition/conjoin [])
          (function/app 'source 'value)
          (function/equality data-level 'A
                             (function/app identity 'value) 'value)
          'source-member
          (function/app
           (function/const* 'equality/reflexive [data-level])
           'A 'value)))))}))

(def bijective-on-identity-spec
  (let [set-a (set-of U 'A)
        identity (identity-map)
        maps (maps-to U U 'A 'A identity 'source 'source)
        injection (injective-on U U 'A 'A identity 'source)
        surjection (surjective-on U U 'A 'A identity 'source 'source)
        target (bijective-on U U 'A 'A identity 'source 'source)]
    {:name 'set/bijective-on-identity
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source set-a]] target)
     :value
     (function/lam
      [['A type-u] ['source set-a]]
      (function/app
       (function/const* 'proposition/conjoin [])
       maps (proposition/conjunction injection surjection)
       (function/app (function/const* 'set/maps-to-identity [U])
                     'A 'source)
       (function/app
        (function/const* 'proposition/conjoin [])
        injection surjection
        (function/app
         (function/const* 'set/injective-on-identity [U])
         'A 'source)
        (function/app
         (function/const* 'set/surjective-on-identity [U])
         'A 'source))))}))

(def maps-to-compose-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        set-c (set-of W 'C)
        composed (compose 'outer 'inner)
        inner-maps (maps-to U V 'A 'B 'inner 'source 'middle)
        outer-maps (maps-to V W 'B 'C 'outer 'middle 'target)
        composed-maps (maps-to U W 'A 'C composed 'source 'target)]
    {:name 'set/maps-to-compose
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a] ['middle set-b] ['target set-c]
       ['inner-maps inner-maps] ['outer-maps outer-maps]]
      composed-maps)
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a] ['middle set-b] ['target set-c]
       ['inner-maps inner-maps] ['outer-maps outer-maps]
       ['value 'A :implicit]
       ['source-member (function/app 'source 'value)]]
      (function/app
       'outer-maps (function/app 'inner 'value)
       (function/app 'inner-maps 'value 'source-member)))}))

(def injective-on-compose-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        composed (compose 'outer 'inner)
        inner-maps (maps-to U V 'A 'B 'inner 'source 'middle)
        inner-injective (injective-on U V 'A 'B 'inner 'source)
        outer-injective (injective-on V W 'B 'C 'outer 'middle)
        composed-injective (injective-on U W 'A 'C composed 'source)]
    {:name 'set/injective-on-compose
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a] ['middle set-b]
       ['inner-maps inner-maps]
       ['inner-injective inner-injective]
       ['outer-injective outer-injective]]
      composed-injective)
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a] ['middle set-b]
       ['inner-maps inner-maps]
       ['inner-injective inner-injective]
       ['outer-injective outer-injective]
       ['left 'A :implicit]
       ['left-member (function/app 'source 'left)]
       ['right 'A :implicit]
       ['right-member (function/app 'source 'right)]
       ['same-composite
        (function/equality
         target-data-level 'C
         (function/app composed 'left)
         (function/app composed 'right))]]
      (function/app
       'inner-injective
       'left 'left-member 'right 'right-member
       (function/app
        'outer-injective
        (function/app 'inner 'left)
        (function/app 'inner-maps 'left 'left-member)
        (function/app 'inner 'right)
        (function/app 'inner-maps 'right 'right-member)
        'same-composite)))}))

(def surjective-on-compose-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        set-c (set-of W 'C)
        composed (compose 'outer 'inner)
        inner-surjective (surjective-on U V 'A 'B 'inner 'source 'middle)
        outer-surjective (surjective-on V W 'B 'C 'outer 'middle 'target)
        composed-surjective
        (surjective-on U W 'A 'C composed 'source 'target)]
    {:name 'set/surjective-on-compose
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a] ['middle set-b] ['target set-c]
       ['inner-surjective inner-surjective]
       ['outer-surjective outer-surjective]]
      composed-surjective)
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a] ['middle set-b] ['target set-c]
       ['inner-surjective inner-surjective]
       ['outer-surjective outer-surjective]
       ['value 'C :implicit]
       ['target-member (function/app 'target 'value)]]
      (let [source-fiber
            (function/lam
             [['source-value 'A]]
             (proposition/conjunction
              (function/app 'source 'source-value)
              (function/equality
               target-data-level 'C
               (function/app composed 'source-value) 'value)))
            source-exists
            (proposition/existence data-level 'A source-fiber)
            middle-fiber
            (function/lam
             [['middle-value 'B]]
             (proposition/conjunction
              (function/app 'middle 'middle-value)
              (function/equality
               target-data-level 'C
               (function/app 'outer 'middle-value) 'value)))]
        (function/app
         (function/const* 'proposition/use-witness [middle-data-level])
         'B middle-fiber source-exists
         (function/app 'outer-surjective 'value 'target-member)
         (function/lam
          [['middle-value 'B]
           ['middle-fiber-evidence
            (function/app middle-fiber 'middle-value)]]
          (let [middle-member
                (function/app
                 (function/const* 'proposition/left [])
                 (function/app 'middle 'middle-value)
                 (function/equality
                  target-data-level 'C
                  (function/app 'outer 'middle-value) 'value)
                 'middle-fiber-evidence)
                middle-maps-target
                (function/app
                 (function/const* 'proposition/right [])
                 (function/app 'middle 'middle-value)
                 (function/equality
                  target-data-level 'C
                  (function/app 'outer 'middle-value) 'value)
                 'middle-fiber-evidence)]
            (function/app
             (function/const* 'proposition/use-witness [data-level])
             'A
             (function/lam
              [['source-value 'A]]
              (proposition/conjunction
               (function/app 'source 'source-value)
               (function/equality
                middle-data-level 'B
                (function/app 'inner 'source-value) 'middle-value)))
             source-exists
             (function/app 'inner-surjective
                           'middle-value middle-member)
             (function/lam
              [['source-value 'A]
               ['source-fiber-evidence
                (proposition/conjunction
                 (function/app 'source 'source-value)
                 (function/equality
                  middle-data-level 'B
                  (function/app 'inner 'source-value) 'middle-value))]]
              (let [source-member
                    (function/app
                     (function/const* 'proposition/left [])
                     (function/app 'source 'source-value)
                     (function/equality
                      middle-data-level 'B
                      (function/app 'inner 'source-value) 'middle-value)
                     'source-fiber-evidence)
                    inner-maps-middle
                    (function/app
                     (function/const* 'proposition/right [])
                     (function/app 'source 'source-value)
                     (function/equality
                      middle-data-level 'B
                      (function/app 'inner 'source-value) 'middle-value)
                     'source-fiber-evidence)
                    composite-maps-middle
                    (function/app
                     (function/const* 'equality/congruent-function
                                      [middle-data-level target-data-level])
                     'B 'C 'outer
                     (function/app 'inner 'source-value) 'middle-value
                     inner-maps-middle)
                    composite-maps-target
                    (function/app
                     (function/const* 'equality/transitive
                                      [target-data-level])
                     'C (function/app composed 'source-value)
                     (function/app 'outer 'middle-value) 'value
                     composite-maps-middle middle-maps-target)]
                (function/app
                 (function/const* 'proposition/witness [data-level])
                 'A source-fiber 'source-value
                 (function/app
                  (function/const* 'proposition/conjoin [])
                  (function/app 'source 'source-value)
                  (function/equality
                   target-data-level 'C
                   (function/app composed 'source-value) 'value)
                  source-member composite-maps-target))))))))))}))

(def bijective-on-compose-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        set-c (set-of W 'C)
        composed (compose 'outer 'inner)
        inner-maps (maps-to U V 'A 'B 'inner 'source 'middle)
        inner-injective (injective-on U V 'A 'B 'inner 'source)
        inner-surjective (surjective-on U V 'A 'B 'inner 'source 'middle)
        inner-bijective (bijective-on U V 'A 'B 'inner 'source 'middle)
        outer-maps (maps-to V W 'B 'C 'outer 'middle 'target)
        outer-injective (injective-on V W 'B 'C 'outer 'middle)
        outer-surjective (surjective-on V W 'B 'C 'outer 'middle 'target)
        outer-bijective (bijective-on V W 'B 'C 'outer 'middle 'target)
        composed-maps (maps-to U W 'A 'C composed 'source 'target)
        composed-injective (injective-on U W 'A 'C composed 'source)
        composed-surjective
        (surjective-on U W 'A 'C composed 'source 'target)
        composed-bijective
        (bijective-on U W 'A 'C composed 'source 'target)]
    {:name 'set/bijective-on-compose
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a] ['middle set-b] ['target set-c]
       ['inner-bijective inner-bijective]
       ['outer-bijective outer-bijective]]
      composed-bijective)
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['inner (function/arrow 'A 'B)]
       ['outer (function/arrow 'B 'C)]
       ['source set-a] ['middle set-b] ['target set-c]
       ['inner-bijective inner-bijective]
       ['outer-bijective outer-bijective]]
      (let [inner-maps-evidence
            (function/app
             (function/const* 'proposition/left [])
             inner-maps
             (proposition/conjunction inner-injective inner-surjective)
             'inner-bijective)
            inner-injective-surjective
            (function/app
             (function/const* 'proposition/right [])
             inner-maps
             (proposition/conjunction inner-injective inner-surjective)
             'inner-bijective)
            inner-injective-evidence
            (function/app (function/const* 'proposition/left [])
                          inner-injective inner-surjective
                          inner-injective-surjective)
            inner-surjective-evidence
            (function/app (function/const* 'proposition/right [])
                          inner-injective inner-surjective
                          inner-injective-surjective)
            outer-maps-evidence
            (function/app
             (function/const* 'proposition/left [])
             outer-maps
             (proposition/conjunction outer-injective outer-surjective)
             'outer-bijective)
            outer-injective-surjective
            (function/app
             (function/const* 'proposition/right [])
             outer-maps
             (proposition/conjunction outer-injective outer-surjective)
             'outer-bijective)
            outer-injective-evidence
            (function/app (function/const* 'proposition/left [])
                          outer-injective outer-surjective
                          outer-injective-surjective)
            outer-surjective-evidence
            (function/app (function/const* 'proposition/right [])
                          outer-injective outer-surjective
                          outer-injective-surjective)]
        (function/app
         (function/const* 'proposition/conjoin [])
         composed-maps
         (proposition/conjunction composed-injective composed-surjective)
         (function/app
          (function/const* 'set/maps-to-compose [U V W])
          'A 'B 'C 'inner 'outer 'source 'middle 'target
          inner-maps-evidence outer-maps-evidence)
         (function/app
          (function/const* 'proposition/conjoin [])
          composed-injective composed-surjective
          (function/app
           (function/const* 'set/injective-on-compose [U V W])
           'A 'B 'C 'inner 'outer 'source 'middle
           inner-maps-evidence inner-injective-evidence
           outer-injective-evidence)
          (function/app
           (function/const* 'set/surjective-on-compose [U V W])
           'A 'B 'C 'inner 'outer 'source 'middle 'target
           inner-surjective-evidence
           outer-surjective-evidence)))))}))

(def theorem-specs
  [maps-to-identity-spec injective-on-identity-spec
   surjective-on-identity-spec bijective-on-identity-spec
   maps-to-compose-spec injective-on-compose-spec
   surjective-on-compose-spec bijective-on-compose-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.set])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :set-map-composition theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.sets.map-composition))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
