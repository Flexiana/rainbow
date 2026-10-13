(ns rainbow.math.logic.exhaustive-carrier-fintype
  "Constructively connect executable exhaustive carriers to extensional Fintype.

  `finset-data/Finset` retains a duplicate-free enumeration in Type, while
  `fintype/Fintype` packages an extensional finite set complete for its ambient
  type.  A certified exhaustive carrier has exactly the evidence needed to map
  in the constructive direction: keep its executable enumeration, project it
  to an extensional finset, and reuse coverage as Fintype completeness.

  The reverse direction is intentionally not claimed: propositional Fintype
  completeness cannot in general be eliminated to recover executable data.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.diagonal-spike :as exhaustive]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def bool (function/const* 'data/Bool []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- extensional-finset-of [element]
  (app (function/const* 'finset/Finset [U]) element))
(defn- to-extensional [element states]
  (app (function/const* 'finset-data/to-extensional [U]) element states))
(defn- finset-set [element states]
  (app (function/const* 'finset/to-set [U]) element states))
(defn- completeness-predicate [element]
  (function/lam
   [['elements (extensional-finset-of element)]]
   (function/forall
    [['value element]]
    (app (finset-set element 'elements) 'value))))
(defn- fintype-of [element]
  (app (function/const* 'fintype/Fintype [U]) element))
(defn- fintype-elements [element instance]
  (app (function/const* 'fintype/elements [U]) element instance))
(defn- exhaustive-carrier [element states decision]
  (app (function/const* 'finite/certified-exhaustive-carrier [U])
       element states decision))
(defn- carrier-fintype [element states decision certificate]
  (app
   (function/const* 'finite/fintype-of-certified-exhaustive-carrier [U])
   element states decision certificate))
(defn- type-finite [element]
  (app (function/const* 'type/finite [data-u]) element))

(def fintype-of-certified-exhaustive-carrier-spec
  {:name 'finite/fintype-of-certified-exhaustive-carrier
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['certificate (exhaustive-carrier 'S 'states 'decision)]]
    (fintype-of 'S))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['certificate (exhaustive-carrier 'S 'states 'decision)]]
    (let [elements (to-extensional 'S 'states)
          covered
          (app
           (function/const* 'finite/coverage-of-exhaustive-carrier [U])
           'S 'states 'decision 'certificate)]
      (app
       (function/const* 'data/subtype [data-u])
       (extensional-finset-of 'S)
       (completeness-predicate 'S)
       elements
       (function/lam [['value 'S]] (app covered 'value)))))})

(def fintype-elements-of-certified-exhaustive-carrier-spec
  {:name 'finite/fintype-elements-of-certified-exhaustive-carrier
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['certificate (exhaustive-carrier 'S 'states 'decision)]]
    (function/equality
     data-u (extensional-finset-of 'S)
     (fintype-elements
      'S (carrier-fintype 'S 'states 'decision 'certificate))
     (to-extensional 'S 'states)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['certificate (exhaustive-carrier 'S 'states 'decision)]]
    (app
     (function/const* 'equality/reflexive [data-u])
     (extensional-finset-of 'S)
     (to-extensional 'S 'states)))})

(def type-finite-of-certified-exhaustive-carrier-spec
  {:name 'finite/type-finite-of-certified-exhaustive-carrier
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['certificate (exhaustive-carrier 'S 'states 'decision)]]
    (type-finite 'S))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['certificate (exhaustive-carrier 'S 'states 'decision)]]
    (app
     (function/const* 'fintype/to-finite [U])
     'S (carrier-fintype 'S 'states 'decision 'certificate)))})

(def definition-specs [fintype-of-certified-exhaustive-carrier-spec])
(def theorem-specs
  [fintype-elements-of-certified-exhaustive-carrier-spec
   type-finite-of-certified-exhaustive-carrier-spec])

(defn extend-environment [env]
  (-> env
      exhaustive/extend-environment
      (support/extend-with
       :exhaustive-carrier-fintype
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
