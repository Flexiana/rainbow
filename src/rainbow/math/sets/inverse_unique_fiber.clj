(ns rainbow.math.sets.inverse-unique-fiber
  "Two-sided set inverses provide unique witnesses in every target fiber."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.sets.fiber-unique :as fiber-unique]
            [rainbow.math.sets.inverse-certificates :as inverse]))

(def U [:param 'u])
(def V [:param 'v])
(def data-level [:succ U])
(def target-data-level [:succ V])
(def type-u [:sort data-level])
(def type-v [:sort target-data-level])

(defn- set-of [level element]
  (function/app (function/const* 'set/Set [level]) element))

(defn- maps-to [source-level target-level source-element target-element
                 mapping source target]
  (function/app (function/const* 'set/maps-to
                                 [source-level target-level])
                source-element target-element mapping source target))

(defn- inverse-on [backward forward source target]
  (function/app (function/const* 'set/inverse-on [U V])
                'A 'B backward forward source target))

(defn- left-inverse-on [backward forward source]
  (function/app (function/const* 'set/left-inverse-on [U V])
                'A 'B backward forward source))

(defn- right-inverse-on [backward forward target]
  (function/app (function/const* 'set/right-inverse-on [U V])
                'A 'B backward forward target))

(defn- fiber-within [mapping source target]
  (function/app (function/const* 'set/fiber-within [U V])
                'A 'B mapping source target))

(def inverse-on-has-unique-fibers-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        forward-maps
        (maps-to U V 'A 'B 'forward 'source 'target)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        inverse-evidence
        (inverse-on 'backward 'forward 'source 'target)
        bijection
        (function/app (function/const* 'set/bijective-on [U V])
                      'A 'B 'forward 'source 'target)
        unique-fibers
        (function/forall
         [['value 'B :implicit]
          ['target-member (function/app 'target 'value)]]
         (proposition/unique-existence
          data-level 'A (fiber-within 'forward 'source 'value)))]
    {:name 'set/inverse-on-has-unique-fibers
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
      unique-fibers)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['forward-maps forward-maps]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]]
      (function/app
       (function/const* 'set/bijective-on-has-unique-fibers [U V])
       'A 'B 'forward 'source 'target
       (function/app
        (function/const* 'set/bijective-on-of-inverse [U V])
        'A 'B 'forward 'backward 'source 'target
        'forward-maps 'backward-maps 'inverse-evidence)))}))

(def inverse-on-backward-in-fiber-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        left-inverse
        (left-inverse-on 'backward 'forward 'source)
        right-inverse
        (right-inverse-on 'backward 'forward 'target)
        inverse-evidence
        (inverse-on 'backward 'forward 'source 'target)
        fiber (fiber-within 'forward 'source 'value)
        result (function/app fiber (function/app 'backward 'value))]
    {:name 'set/inverse-on-backward-in-fiber
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]
       ['value 'B] ['target-member (function/app 'target 'value)]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]
       ['value 'B] ['target-member (function/app 'target 'value)]]
      (function/app
       (function/const* 'proposition/conjoin [])
       (function/app 'source (function/app 'backward 'value))
       (function/equality
        target-data-level 'B
        (function/app 'forward (function/app 'backward 'value)) 'value)
       (function/app 'backward-maps 'value 'target-member)
       (function/app
        (function/app
         (function/const* 'proposition/right [])
         left-inverse right-inverse 'inverse-evidence)
        'value 'target-member)))}))

(def inverse-on-fiber-member-equals-backward-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        left-inverse
        (left-inverse-on 'backward 'forward 'source)
        right-inverse
        (right-inverse-on 'backward 'forward 'target)
        inverse-evidence
        (inverse-on 'backward 'forward 'source 'target)
        fiber (fiber-within 'forward 'source 'value)]
    {:name 'set/inverse-on-fiber-member-equals-backward
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['inverse-evidence inverse-evidence]
       ['value 'B] ['candidate 'A]
       ['candidate-fiber (function/app fiber 'candidate)]]
      (function/equality data-level 'A
                         'candidate (function/app 'backward 'value)))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['inverse-evidence inverse-evidence]
       ['value 'B] ['candidate 'A]
       ['candidate-fiber (function/app fiber 'candidate)]]
      (let [candidate-source
            (function/app
             (function/const* 'set/fiber-within-member-source [U V])
             'A 'B 'forward 'source 'value
             'candidate 'candidate-fiber)
            candidate-maps-value
            (function/app
             (function/const* 'set/fiber-within-mapping-equals [U V])
             'A 'B 'forward 'source 'value
             'candidate 'candidate-fiber)
            left-law
            (function/app
             (function/app
              (function/const* 'proposition/left [])
              left-inverse right-inverse 'inverse-evidence)
             'candidate candidate-source)
            candidate-to-roundtrip
            (function/app
             (function/const* 'equality/symmetric [data-level])
             'A
             (function/app 'backward
                           (function/app 'forward 'candidate))
             'candidate left-law)
            roundtrip-to-backward
            (function/app
             (function/const* 'equality/congruent-function
                              [target-data-level data-level])
             'B 'A 'backward
             (function/app 'forward 'candidate) 'value
             candidate-maps-value)]
        (function/app
         (function/const* 'equality/transitive [data-level])
         'A 'candidate
         (function/app 'backward (function/app 'forward 'candidate))
         (function/app 'backward 'value)
         candidate-to-roundtrip roundtrip-to-backward)))}))

(def inverse-on-has-canonical-unique-fibers-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        backward-maps
        (maps-to V U 'B 'A 'backward 'target 'source)
        inverse-evidence
        (inverse-on 'backward 'forward 'source 'target)
        result
        (function/forall
         [['value 'B :implicit]
          ['target-member (function/app 'target 'value)]]
         (let [fiber (fiber-within 'forward 'source 'value)
               backward-value (function/app 'backward 'value)]
           (proposition/conjunction
            (function/app fiber backward-value)
            (proposition/uniqueness
             data-level 'A fiber backward-value))))]
    {:name 'set/inverse-on-has-canonical-unique-fibers
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]]
      result)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['forward (function/arrow 'A 'B)]
       ['backward (function/arrow 'B 'A)]
       ['source set-a] ['target set-b]
       ['backward-maps backward-maps]
       ['inverse-evidence inverse-evidence]
       ['value 'B :implicit]
       ['target-member (function/app 'target 'value)]]
      (let [fiber (fiber-within 'forward 'source 'value)
            backward-value (function/app 'backward 'value)]
        (function/app
         (function/const* 'proposition/conjoin [])
         (function/app fiber backward-value)
         (proposition/uniqueness data-level 'A fiber backward-value)
         (function/app
          (function/const* 'set/inverse-on-backward-in-fiber [U V])
          'A 'B 'forward 'backward 'source 'target
          'backward-maps 'inverse-evidence 'value 'target-member)
         (function/lam
          [['candidate 'A]
           ['candidate-fiber (function/app fiber 'candidate)]]
          (function/app
           (function/const*
            'set/inverse-on-fiber-member-equals-backward [U V])
           'A 'B 'forward 'backward 'source 'target
           'inverse-evidence 'value 'candidate 'candidate-fiber)))))}))

(def theorem-specs
  [inverse-on-has-unique-fibers-spec
   inverse-on-backward-in-fiber-spec
   inverse-on-fiber-member-equals-backward-spec
   inverse-on-has-canonical-unique-fibers-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      inverse/extend-environment
      fiber-unique/extend-environment
      (support/extend-with :set-inverse-unique-fiber theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
