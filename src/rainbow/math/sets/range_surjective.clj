(ns rainbow.math.sets.range-surjective
  "Characterize surjections by their universal ranges."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.sets.range-image-bridge :as range-image]))

(def U [:param 'u])
(def V [:param 'v])
(def data-level [:succ U])
(def target-data-level [:succ V])
(def type-u [:sort data-level])
(def type-v [:sort target-data-level])

(defn- universal [level element]
  (function/app (function/const* 'set/universal [level]) element))

(defn- range-set [mapping]
  (function/app (function/const* 'set/range [U V])
                'A 'B mapping))

(defn- subset [small large]
  (function/app (function/const* 'set/subset [V])
                'B small large))

(defn- mutual-subset [left right]
  (proposition/conjunction (subset left right)
                           (subset right left)))

(defn- surjective [mapping]
  (function/surjective data-level target-data-level
                        'A 'B mapping))

(def range-subset-universal-spec
  (let [range (range-set 'mapping)
        universal-b (universal V 'B)]
    {:name 'set/range-subset-universal
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]]
      (subset range universal-b))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['value 'B] ['range-member (function/app range 'value)]]
      (function/const* 'proposition/trivial []))}))

(def universal-subset-range-of-surjective-spec
  (let [range (range-set 'mapping)
        universal-b (universal V 'B)
        surjection (surjective 'mapping)
        covers (subset universal-b range)]
    {:name 'set/universal-subset-range-of-surjective
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['surjection-evidence surjection]]
      covers)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['surjection-evidence surjection]]
      (function/app
       (function/const* 'proposition/equivalence-forward [])
       surjection covers
       (function/app
        (function/const*
         'function/surjective-equivalent-universal-subset-range [U V])
        'A 'B 'mapping)
       'surjection-evidence))}))

(def range-universal-mutual-subset-of-surjective-spec
  (let [range (range-set 'mapping)
        universal-b (universal V 'B)
        forward (subset range universal-b)
        backward (subset universal-b range)
        surjection (surjective 'mapping)]
    {:name 'set/range-universal-mutual-subset-of-surjective
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['surjection-evidence surjection]]
      (proposition/conjunction forward backward))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['surjection-evidence surjection]]
      (function/app
       (function/const* 'proposition/conjoin [])
       forward backward
       (function/app
        (function/const* 'set/range-subset-universal [U V])
        'A 'B 'mapping)
       (function/app
        (function/const* 'set/universal-subset-range-of-surjective [U V])
        'A 'B 'mapping 'surjection-evidence)))}))

(def surjective-equivalent-range-universal-mutual-subset-spec
  (let [range (range-set 'mapping)
        universal-b (universal V 'B)
        surjection (surjective 'mapping)
        forward (subset range universal-b)
        backward (subset universal-b range)
        equivalent (proposition/conjunction forward backward)
        covers-equivalence
        (function/app
         (function/const*
          'function/surjective-equivalent-universal-subset-range [U V])
         'A 'B 'mapping)]
    {:name 'function/surjective-equivalent-range-universal-mutual-subset
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]]
      (proposition/equivalence surjection equivalent))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       surjection equivalent
       (function/lam
        [['surjection-evidence surjection]]
        (function/app
         (function/const*
          'set/range-universal-mutual-subset-of-surjective [U V])
         'A 'B 'mapping 'surjection-evidence))
       (function/lam
        [['mutual-subset-evidence equivalent]]
        (let [covers
              (function/app
               (function/const* 'proposition/right [])
               forward backward 'mutual-subset-evidence)]
          (function/app
           (function/const* 'proposition/equivalence-backward [])
           surjection backward covers-equivalence covers)))))}))

(def theorem-specs
  [range-subset-universal-spec
   universal-subset-range-of-surjective-spec
   range-universal-mutual-subset-of-surjective-spec
   surjective-equivalent-range-universal-mutual-subset-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      range-image/extend-environment
      (support/extend-with :set-range-surjective theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
