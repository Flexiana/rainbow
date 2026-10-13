(ns rainbow.math.finite.set-fiber
  "Constructive finite fibers inside finite source sets."
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

(defn- equality [element left right]
  (function/equality target-data-level element left right))

(defn- subset [element small large]
  (function/app (function/const* 'set/subset [U])
                element small large))

(defn- finite [element source]
  (function/app (function/const* 'set/finite [U]) element source))

(defn- fiber-within [source-element target-element mapping source target]
  (function/app (function/const* 'set/fiber-within [U V])
                source-element target-element mapping source target))

(def fiber-within-spec
  {:name 'set/fiber-within
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['A type-u] ['B type-v]
     ['mapping (function/arrow 'A 'B)]
     ['source (set-of U 'A)]
     ['target 'B]]
    (set-of U 'A))
   :value
   (function/lam
    [['A type-u] ['B type-v]
     ['mapping (function/arrow 'A 'B)]
     ['source (set-of U 'A)]
     ['target 'B]
     ['value 'A]]
    (proposition/conjunction
     (function/app 'source 'value)
     (equality 'B (function/app 'mapping 'value) 'target)))})

(def fiber-within-subset-spec
  (let [fiber (fiber-within 'A 'B 'mapping 'source 'target)]
    {:name 'set/fiber-within-subset
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['target 'B]]
      (subset 'A fiber 'source))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['target 'B]
       ['value 'A]
       ['member (function/app fiber 'value)]]
      (function/app (function/const* 'proposition/left [])
       (function/app 'source 'value)
       (equality 'B (function/app 'mapping 'value) 'target)
       'member))}))

(def fiber-within-member-source-spec
  (let [fiber (fiber-within 'A 'B 'mapping 'source 'target)]
    {:name 'set/fiber-within-member-source
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['target 'B]
       ['value 'A]
       ['member (function/app fiber 'value)]]
      (function/app 'source 'value))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['target 'B]
       ['value 'A]
       ['member (function/app fiber 'value)]]
      (function/app (function/const* 'proposition/left [])
       (function/app 'source 'value)
       (equality 'B (function/app 'mapping 'value) 'target)
       'member))}))

(def fiber-within-mapping-equals-spec
  (let [fiber (fiber-within 'A 'B 'mapping 'source 'target)]
    {:name 'set/fiber-within-mapping-equals
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['target 'B]
       ['value 'A]
       ['member (function/app fiber 'value)]]
      (equality 'B (function/app 'mapping 'value) 'target))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['target 'B]
       ['value 'A]
       ['member (function/app fiber 'value)]]
      (function/app (function/const* 'proposition/right [])
       (function/app 'source 'value)
       (equality 'B (function/app 'mapping 'value) 'target)
       'member))}))

(def finite-fiber-within-spec
  (let [fiber (fiber-within 'A 'B 'mapping 'source 'target)]
    {:name 'set/finite-fiber-within
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['target 'B]
       ['source-finite (finite 'A 'source)]]
      (finite 'A fiber))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source (set-of U 'A)]
       ['target 'B]
       ['source-finite (finite 'A 'source)]]
      (function/app
       (function/const* 'set/finite-subset-preserved [U])
       'A fiber 'source
       (function/app
        (function/const* 'set/fiber-within-subset [U V])
        'A 'B 'mapping 'source 'target)
       'source-finite))}))

(def definition-specs [fiber-within-spec])

(def theorem-specs
  [fiber-within-subset-spec
   fiber-within-member-source-spec
   fiber-within-mapping-equals-spec
   finite-fiber-within-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      finite-set/extend-environment
      (support/extend-with :finite-set-fiber
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
