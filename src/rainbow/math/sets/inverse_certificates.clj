(ns rainbow.math.sets.inverse-certificates
  "Constructive injectivity, surjectivity, and bijectivity from set inverses."
  (:require [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def data-level [:succ U])
(def target-data-level [:succ V])
(def output-data-level [:succ W])
(def type-u [:sort data-level])
(def type-v [:sort target-data-level])
(def type-w [:sort output-data-level])

(defn- set-of [level element]
  (function/app (function/const* 'set/Set [level]) element))

(defn- compose-map [source-level middle-level output-level
                    source-element middle-element output-element outer inner]
  (function/app
   (function/const* 'function/compose
                    [source-level middle-level output-level])
   source-element middle-element output-element outer inner))

(defn- maps-to [source-level target-level source-element target-element
                 mapping source target]
  (function/app (function/const* 'set/maps-to
                                 [source-level target-level])
                source-element target-element mapping source target))

(defn- injective-on [mapping source]
  (function/app (function/const* 'set/injective-on [U V])
                'A 'B mapping source))

(defn- surjective-on [mapping source target]
  (function/app (function/const* 'set/surjective-on [U V])
                'A 'B mapping source target))

(defn- bijective-on [mapping source target]
  (function/app (function/const* 'set/bijective-on [U V])
                'A 'B mapping source target))

(defn- left-inverse-on [source-level target-level source-element target-element
                        backward forward source]
  (function/app (function/const* 'set/left-inverse-on
                                 [source-level target-level])
                source-element target-element backward forward source))

(defn- right-inverse-on [source-level target-level source-element target-element
                         backward forward target]
  (function/app (function/const* 'set/right-inverse-on
                                 [source-level target-level])
                source-element target-element backward forward target))

(defn- inverse-on [source-level target-level source-element target-element
                   backward forward source target]
  (function/app (function/const* 'set/inverse-on
                                 [source-level target-level])
                source-element target-element backward forward source target))

(def injective-on-of-left-inverse-spec
  (let [set-a (set-of U 'A)
        left-inverse
        (left-inverse-on U V 'A 'B 'backward 'forward 'source)
        target (injective-on 'forward 'source)]
    {:name 'set/injective-on-of-left-inverse
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a]
       ['left-inverse left-inverse]]
      target)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a]
       ['left-inverse left-inverse]
       ['left 'A :implicit]
       ['left-member (function/app 'source 'left)]
       ['right 'A :implicit]
       ['right-member (function/app 'source 'right)]
       ['same-image
        (function/equality target-data-level 'B
                           (function/app 'forward 'left)
                           (function/app 'forward 'right))]]
      (let [backward-left
            (function/app 'backward (function/app 'forward 'left))
            backward-right
            (function/app 'backward (function/app 'forward 'right))
            left-law (function/app 'left-inverse 'left 'left-member)
            right-law (function/app 'left-inverse 'right 'right-member)
            backward-congruent
            (function/app
             (function/const* 'equality/congruent-function
                              [target-data-level data-level])
             'B 'A 'backward
             (function/app 'forward 'left)
             (function/app 'forward 'right)
             'same-image)
            left-to-backward-left
            (function/app
             (function/const* 'equality/symmetric [data-level])
             'A backward-left 'left left-law)
            left-to-backward-right
            (function/app
             (function/const* 'equality/transitive [data-level])
             'A 'left backward-left backward-right
             left-to-backward-left backward-congruent)]
        (function/app
         (function/const* 'equality/transitive [data-level])
         'A 'left backward-right 'right
         left-to-backward-right right-law)))}))

(def surjective-on-of-right-inverse-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        right-inverse
        (right-inverse-on U V 'A 'B 'backward 'forward 'target)
        result (surjective-on 'forward 'source 'target)]
    {:name 'set/surjective-on-of-right-inverse
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['backward-maps backward-maps]
       ['right-inverse right-inverse]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['backward-maps backward-maps]
       ['right-inverse right-inverse]
       ['value 'B :implicit]
       ['target-member (function/app 'target 'value)]]
      (let [fiber
            (function/lam
             [['candidate 'A]]
             (proposition/conjunction
              (function/app 'source 'candidate)
              (function/equality target-data-level 'B
                                 (function/app 'forward 'candidate)
                                 'value)))]
        (function/app
         (function/const* 'proposition/witness [data-level])
         'A fiber (function/app 'backward 'value)
         (function/app
          (function/const* 'proposition/conjoin [])
          (function/app 'source (function/app 'backward 'value))
          (function/equality
           target-data-level 'B
           (function/app 'forward (function/app 'backward 'value))
           'value)
          (function/app 'backward-maps 'value 'target-member)
          (function/app 'right-inverse 'value 'target-member)))))}))

(def bijective-on-of-inverse-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        forward-maps
        (maps-to U V 'A 'B 'forward 'source 'target)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        left-inverse
        (left-inverse-on U V 'A 'B 'backward 'forward 'source)
        right-inverse
        (right-inverse-on U V 'A 'B 'backward 'forward 'target)
        inverse
        (inverse-on U V 'A 'B 'backward 'forward 'source 'target)
        injection (injective-on 'forward 'source)
        surjection (surjective-on 'forward 'source 'target)
        result (bijective-on 'forward 'source 'target)]
    {:name 'set/bijective-on-of-inverse
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse]]
      (let [left-inverse-evidence
            (function/app (function/const* 'proposition/left [])
                          left-inverse right-inverse 'inverse-evidence)
            right-inverse-evidence
            (function/app (function/const* 'proposition/right [])
                          left-inverse right-inverse 'inverse-evidence)]
        (function/app
         (function/const* 'proposition/conjoin [])
         forward-maps (proposition/conjunction injection surjection)
         'forward-maps
         (function/app
          (function/const* 'proposition/conjoin [])
          injection surjection
          (function/app
           (function/const* 'set/injective-on-of-left-inverse [U V])
           'A 'B 'forward 'backward 'source left-inverse-evidence)
          (function/app
           (function/const* 'set/surjective-on-of-right-inverse [U V])
           'A 'B 'forward 'backward 'source 'target
           'backward-maps right-inverse-evidence)))))}))

(def inverse-on-symmetric-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        left-inverse
        (left-inverse-on U V 'A 'B 'backward 'forward 'source)
        right-inverse
        (right-inverse-on U V 'A 'B 'backward 'forward 'target)
        original
        (inverse-on U V 'A 'B 'backward 'forward 'source 'target)
        reversed-left
        (left-inverse-on V U 'B 'A 'forward 'backward 'target)
        reversed-right
        (right-inverse-on V U 'B 'A 'forward 'backward 'source)
        reversed
        (inverse-on V U 'B 'A 'forward 'backward 'target 'source)]
    {:name 'set/inverse-on-symmetric
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['inverse-evidence original]]
      reversed)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['inverse-evidence original]]
      (function/app
       (function/const* 'proposition/conjoin [])
       reversed-left reversed-right
       (function/app (function/const* 'proposition/right [])
                     left-inverse right-inverse 'inverse-evidence)
       (function/app (function/const* 'proposition/left [])
                     left-inverse right-inverse 'inverse-evidence)))}))

(def inverse-on-compose-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        set-c (set-of W 'C)
        forward-composed
        (compose-map data-level target-data-level output-data-level
                     'A 'B 'C 'forward-two 'forward-one)
        backward-composed
        (compose-map output-data-level target-data-level data-level
                     'C 'B 'A 'backward-one 'backward-two)
        forward-one-maps
        (maps-to U V 'A 'B 'forward-one 'source 'middle)
        backward-two-maps
        (maps-to W V 'C 'B 'backward-two 'target 'middle)
        left-one
        (left-inverse-on U V 'A 'B
                         'backward-one 'forward-one 'source)
        right-one
        (right-inverse-on U V 'A 'B
                          'backward-one 'forward-one 'middle)
        inverse-one
        (inverse-on U V 'A 'B
                    'backward-one 'forward-one 'source 'middle)
        left-two
        (left-inverse-on V W 'B 'C
                         'backward-two 'forward-two 'middle)
        right-two
        (right-inverse-on V W 'B 'C
                          'backward-two 'forward-two 'target)
        inverse-two
        (inverse-on V W 'B 'C
                    'backward-two 'forward-two 'middle 'target)
        composed-left
        (left-inverse-on U W 'A 'C
                         backward-composed forward-composed 'source)
        composed-right
        (right-inverse-on U W 'A 'C
                          backward-composed forward-composed 'target)
        result
        (inverse-on U W 'A 'C
                    backward-composed forward-composed 'source 'target)]
    {:name 'set/inverse-on-compose
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['forward-one (function/arrow 'A 'B)]
       ['backward-one (function/arrow 'B 'A)]
       ['forward-two (function/arrow 'B 'C)]
       ['backward-two (function/arrow 'C 'B)]
       ['source set-a] ['middle set-b] ['target set-c]
       ['forward-one-maps forward-one-maps]
       ['backward-two-maps backward-two-maps]
       ['inverse-one-evidence inverse-one]
       ['inverse-two-evidence inverse-two]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['forward-one (function/arrow 'A 'B)]
       ['backward-one (function/arrow 'B 'A)]
       ['forward-two (function/arrow 'B 'C)]
       ['backward-two (function/arrow 'C 'B)]
       ['source set-a] ['middle set-b] ['target set-c]
       ['forward-one-maps forward-one-maps]
       ['backward-two-maps backward-two-maps]
       ['inverse-one-evidence inverse-one]
       ['inverse-two-evidence inverse-two]]
      (let [left-one-evidence
            (function/app (function/const* 'proposition/left [])
                          left-one right-one 'inverse-one-evidence)
            right-one-evidence
            (function/app (function/const* 'proposition/right [])
                          left-one right-one 'inverse-one-evidence)
            left-two-evidence
            (function/app (function/const* 'proposition/left [])
                          left-two right-two 'inverse-two-evidence)
            right-two-evidence
            (function/app (function/const* 'proposition/right [])
                          left-two right-two 'inverse-two-evidence)
            composed-left-evidence
            (function/lam
             [['value 'A :implicit]
              ['source-member (function/app 'source 'value)]]
             (let [middle-value (function/app 'forward-one 'value)
                   middle-member
                   (function/app 'forward-one-maps
                                 'value 'source-member)
                   second-left
                   (function/app left-two-evidence
                                 middle-value middle-member)
                   first-congruent
                   (function/app
                    (function/const* 'equality/congruent-function
                                     [target-data-level data-level])
                    'B 'A 'backward-one
                    (function/app
                     'backward-two
                     (function/app 'forward-two middle-value))
                    middle-value second-left)
                   first-left
                   (function/app left-one-evidence
                                 'value 'source-member)]
               (function/app
                (function/const* 'equality/transitive [data-level])
                'A (function/app backward-composed
                                 (function/app forward-composed 'value))
                (function/app 'backward-one middle-value)
                'value first-congruent first-left)))
            composed-right-evidence
            (function/lam
             [['value 'C :implicit]
              ['target-member (function/app 'target 'value)]]
             (let [middle-value (function/app 'backward-two 'value)
                   middle-member
                   (function/app 'backward-two-maps
                                 'value 'target-member)
                   first-right
                   (function/app right-one-evidence
                                 middle-value middle-member)
                   second-congruent
                   (function/app
                    (function/const* 'equality/congruent-function
                                     [target-data-level output-data-level])
                    'B 'C 'forward-two
                    (function/app
                     'forward-one
                     (function/app 'backward-one middle-value))
                    middle-value first-right)
                   second-right
                   (function/app right-two-evidence
                                 'value 'target-member)]
               (function/app
                (function/const* 'equality/transitive [output-data-level])
                'C (function/app forward-composed
                                 (function/app backward-composed 'value))
                (function/app 'forward-two middle-value)
                'value second-congruent second-right)))]
        (function/app
         (function/const* 'proposition/conjoin [])
         composed-left composed-right
         composed-left-evidence composed-right-evidence)))}))

(def theorem-specs
  [injective-on-of-left-inverse-spec
   surjective-on-of-right-inverse-spec
   bijective-on-of-inverse-spec
   inverse-on-symmetric-spec
   inverse-on-compose-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      finite-set/extend-environment
      (support/extend-with :set-inverse-certificates theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
