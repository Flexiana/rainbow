(ns rainbow.math.finite.set-inverse-transport
  "Constructive finiteness and infinitude transport across explicit set inverses."
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

(defn- finite [level element source]
  (function/app (function/const* 'set/finite [level]) element source))

(defn- infinite [level element source]
  (function/app (function/const* 'set/infinite [level]) element source))

(defn- nonempty [level element source]
  (function/app (function/const* 'set/nonempty [level]) element source))

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

(defn- inverse-on [source-level target-level source-element target-element
                   backward forward source target]
  (function/app (function/const* 'set/inverse-on
                                 [source-level target-level])
                source-element target-element backward forward source target))

(def nonempty-of-maps-to-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        maps (maps-to U V 'A 'B 'mapping 'source 'target)
        source-nonempty (nonempty U 'A 'source)
        target-nonempty (nonempty V 'B 'target)]
    {:name 'set/nonempty-of-maps-to
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['maps-evidence maps]
       ['source-nonempty-evidence source-nonempty]]
      target-nonempty)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['maps-evidence maps]
       ['source-nonempty-evidence source-nonempty]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A 'source target-nonempty 'source-nonempty-evidence
       (function/lam
        [['value 'A] ['source-member (function/app 'source 'value)]]
        (function/app
         (function/const* 'proposition/witness [target-data-level])
         'B 'target (function/app 'mapping 'value)
         (function/app 'maps-evidence 'value 'source-member)))))}))

(def nonempty-equivalent-of-mutual-maps-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        forward-maps
        (maps-to U V 'A 'B 'forward 'source 'target)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        source-nonempty (nonempty U 'A 'source)
        target-nonempty (nonempty V 'B 'target)]
    {:name 'set/nonempty-equivalent-of-mutual-maps
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]]
      (proposition/equivalence source-nonempty target-nonempty))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       source-nonempty target-nonempty
       (function/lam
        [['source-nonempty-evidence source-nonempty]]
        (function/app
         (function/const* 'set/nonempty-of-maps-to [U V])
         'A 'B 'forward 'source 'target
         'forward-maps 'source-nonempty-evidence))
       (function/lam
        [['target-nonempty-evidence target-nonempty]]
        (function/app
         (function/const* 'set/nonempty-of-maps-to [V U])
         'B 'A 'backward 'target 'source
         'backward-maps 'target-nonempty-evidence))))}))

(def finite-equivalent-of-inverse-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        forward-maps
        (maps-to U V 'A 'B 'forward 'source 'target)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        inverse-evidence
        (inverse-on U V 'A 'B 'backward 'forward 'source 'target)
        source-finite (finite U 'A 'source)
        target-finite (finite V 'B 'target)
        forward-injective
        (injective-on U V 'A 'B 'forward 'source)
        forward-surjective
        (surjective-on U V 'A 'B 'forward 'source 'target)
        forward-bijective
        (bijective-on U V 'A 'B 'forward 'source 'target)
        reverse-injective
        (injective-on V U 'B 'A 'backward 'target)
        reverse-surjective
        (surjective-on V U 'B 'A 'backward 'target 'source)
        reverse-bijective
        (bijective-on V U 'B 'A 'backward 'target 'source)]
    {:name 'set/finite-equivalent-of-inverse
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
      (proposition/equivalence source-finite target-finite))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]]
      (let [forward-bijection-evidence
            (function/app
             (function/const* 'set/bijective-on-of-inverse [U V])
             'A 'B 'forward 'backward 'source 'target
             'forward-maps 'backward-maps 'inverse-evidence)
            forward-injective-surjective
            (function/app
             (function/const* 'proposition/right [])
             forward-maps
             (proposition/conjunction
              forward-injective forward-surjective)
             forward-bijection-evidence)
            forward-surjection-evidence
            (function/app
             (function/const* 'proposition/right [])
             forward-injective forward-surjective
             forward-injective-surjective)
            reverse-inverse-evidence
            (function/app
             (function/const* 'set/inverse-on-symmetric [U V])
             'A 'B 'forward 'backward 'source 'target 'inverse-evidence)
            reverse-bijection-evidence
            (function/app
             (function/const* 'set/bijective-on-of-inverse [V U])
             'B 'A 'backward 'forward 'target 'source
             'backward-maps 'forward-maps reverse-inverse-evidence)
            reverse-injective-surjective
            (function/app
             (function/const* 'proposition/right [])
             backward-maps
             (proposition/conjunction
              reverse-injective reverse-surjective)
             reverse-bijection-evidence)
            reverse-surjection-evidence
            (function/app
             (function/const* 'proposition/right [])
             reverse-injective reverse-surjective
             reverse-injective-surjective)]
        (function/app
         (function/const* 'proposition/equivalence-intro [])
         source-finite target-finite
         (function/lam
          [['source-finite-evidence source-finite]]
          (function/app
           (function/const* 'set/finite-of-surjection [U V])
           'A 'B 'source 'target 'forward
           forward-surjection-evidence 'source-finite-evidence))
         (function/lam
          [['target-finite-evidence target-finite]]
          (function/app
           (function/const* 'set/finite-of-surjection [V U])
           'B 'A 'target 'source 'backward
           reverse-surjection-evidence 'target-finite-evidence)))))}))

(def infinite-equivalent-of-inverse-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        forward-maps
        (maps-to U V 'A 'B 'forward 'source 'target)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        inverse-evidence
        (inverse-on U V 'A 'B 'backward 'forward 'source 'target)
        source-finite (finite U 'A 'source)
        target-finite (finite V 'B 'target)
        source-infinite (infinite U 'A 'source)
        target-infinite (infinite V 'B 'target)]
    {:name 'set/infinite-equivalent-of-inverse
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
      (proposition/equivalence source-infinite target-infinite))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]]
      (let [finite-equivalence
            (function/app
             (function/const* 'set/finite-equivalent-of-inverse [U V])
             'A 'B 'forward 'backward 'source 'target
             'forward-maps 'backward-maps 'inverse-evidence)]
        (function/app
         (function/const* 'proposition/equivalence-intro [])
         source-infinite target-infinite
         (function/lam
          [['source-infinite-evidence source-infinite]
           ['target-finite-evidence target-finite]]
          (function/app
           'source-infinite-evidence
           (function/app
            (function/const* 'proposition/equivalence-backward [])
            source-finite target-finite finite-equivalence
            'target-finite-evidence)))
         (function/lam
          [['target-infinite-evidence target-infinite]
           ['source-finite-evidence source-finite]]
          (function/app
           'target-infinite-evidence
           (function/app
            (function/const* 'proposition/equivalence-forward [])
            source-finite target-finite finite-equivalence
            'source-finite-evidence))))))}))

(def finite-nonempty-equivalent-of-inverse-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        forward-maps
        (maps-to U V 'A 'B 'forward 'source 'target)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        inverse-evidence
        (inverse-on U V 'A 'B 'backward 'forward 'source 'target)
        source-finite (finite U 'A 'source)
        target-finite (finite V 'B 'target)
        source-nonempty (nonempty U 'A 'source)
        target-nonempty (nonempty V 'B 'target)
        source-condition
        (proposition/conjunction source-finite source-nonempty)
        target-condition
        (proposition/conjunction target-finite target-nonempty)]
    {:name 'set/finite-nonempty-equivalent-of-inverse
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
      (proposition/equivalence source-condition target-condition))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]]
      (let [finite-equivalence
            (function/app
             (function/const* 'set/finite-equivalent-of-inverse [U V])
             'A 'B 'forward 'backward 'source 'target
             'forward-maps 'backward-maps 'inverse-evidence)
            nonempty-equivalence
            (function/app
             (function/const*
              'set/nonempty-equivalent-of-mutual-maps [U V])
             'A 'B 'forward 'backward 'source 'target
             'forward-maps 'backward-maps)]
        (function/app
         (function/const* 'proposition/equivalence-intro [])
         source-condition target-condition
         (function/lam
          [['source-condition-evidence source-condition]]
          (function/app
           (function/const* 'proposition/conjoin [])
           target-finite target-nonempty
           (function/app
            (function/const* 'proposition/equivalence-forward [])
            source-finite target-finite finite-equivalence
            (function/app
             (function/const* 'proposition/left [])
             source-finite source-nonempty 'source-condition-evidence))
           (function/app
            (function/const* 'proposition/equivalence-forward [])
            source-nonempty target-nonempty nonempty-equivalence
            (function/app
             (function/const* 'proposition/right [])
             source-finite source-nonempty 'source-condition-evidence))))
         (function/lam
          [['target-condition-evidence target-condition]]
          (function/app
           (function/const* 'proposition/conjoin [])
           source-finite source-nonempty
           (function/app
            (function/const* 'proposition/equivalence-backward [])
            source-finite target-finite finite-equivalence
            (function/app
             (function/const* 'proposition/left [])
             target-finite target-nonempty 'target-condition-evidence))
           (function/app
            (function/const* 'proposition/equivalence-backward [])
            source-nonempty target-nonempty nonempty-equivalence
            (function/app
             (function/const* 'proposition/right [])
             target-finite target-nonempty
             'target-condition-evidence)))))))}))

(def theorem-specs
  [nonempty-of-maps-to-spec
   nonempty-equivalent-of-mutual-maps-spec
   finite-equivalent-of-inverse-spec
   infinite-equivalent-of-inverse-spec
   finite-nonempty-equivalent-of-inverse-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      inverse/extend-environment
      (support/extend-with :finite-set-inverse-transport theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
