(ns rainbow.math.finite.markov-kernel-composition-positive
  "Positive witnesses for finite exact-rational kernel composition.

  A listed intermediate with positive entries in both factor kernels witnesses
  a positive entry in their composition.  The proof multiplies the two
  positive entries and retains that term through the finite sum.  This is the
  algebraic path-concatenation rule for reachability.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.markov-kernel-composition :as composition]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.map-sum-positive :as positive-sum]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- membership [element items value]
  (app (function/const* 'list/membership [U]) element items value))
(defn- carrier-covered [element states]
  (function/forall
   [['state element]]
   (membership element (enumeration element states) 'state)))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- positive [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- kernel-compose
  [element states first-kernel second-kernel source target]
  (app (function/const* 'markov/nnrat-kernel-compose [U])
       element states first-kernel second-kernel source target))

(def kernel-compose-positive-of-member-spec
  {:name 'markov/nnrat-kernel-compose-positive-of-member
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['source 'S] ['middle 'S] ['target 'S]
     ['middle-member
      (membership 'S (enumeration 'S 'states) 'middle)]
     ['first-positive
      (positive (app 'first-kernel 'source 'middle))]
     ['second-positive
      (positive (app 'second-kernel 'middle 'target))]]
    (positive
     (kernel-compose
      'S 'states 'first-kernel 'second-kernel 'source 'target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['source 'S] ['middle 'S] ['target 'S]
     ['middle-member
      (membership 'S (enumeration 'S 'states) 'middle)]
     ['first-positive
      (positive (app 'first-kernel 'source 'middle))]
     ['second-positive
      (positive (app 'second-kernel 'middle 'target))]]
    (let [path-products
          (function/lam
           [['candidate 'S]]
           (rmul
            (app 'first-kernel 'source 'candidate)
            (app 'second-kernel 'candidate 'target)))
          witness-positive
          (app
           (function/const* 'nnrat/multiply-positive [])
           (app 'first-kernel 'source 'middle)
           (app 'second-kernel 'middle 'target)
           'first-positive 'second-positive)]
      (app
       (function/const* 'nnrat/map-sum-positive-of-member [U])
       'S path-products (enumeration 'S 'states)
       'middle 'middle-member witness-positive)))})

(def kernel-compose-pointwise-positive-spec
  {:name 'markov/nnrat-kernel-compose-pointwise-positive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['covered (carrier-covered 'S 'states)]
     ['first-positive
      (function/forall
       [['left 'S] ['right 'S]]
       (positive (app 'first-kernel 'left 'right)))]
     ['second-positive
      (function/forall
       [['left 'S] ['right 'S]]
       (positive (app 'second-kernel 'left 'right)))]]
    (function/forall
     [['source 'S] ['target 'S]]
     (positive
      (kernel-compose
       'S 'states 'first-kernel 'second-kernel 'source 'target))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['covered (carrier-covered 'S 'states)]
     ['first-positive
      (function/forall
       [['left 'S] ['right 'S]]
       (positive (app 'first-kernel 'left 'right)))]
     ['second-positive
      (function/forall
       [['left 'S] ['right 'S]]
       (positive (app 'second-kernel 'left 'right)))]]
    (function/lam
     [['source 'S] ['target 'S]]
     (app
      (function/const*
       'markov/nnrat-kernel-compose-positive-of-member [U])
      'S 'states 'first-kernel 'second-kernel
      'source 'source 'target
      (app 'covered 'source)
      (app 'first-positive 'source 'source)
      (app 'second-positive 'source 'target))))})

(def definition-specs [])
(def theorem-specs
  [kernel-compose-positive-of-member-spec
   kernel-compose-pointwise-positive-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.map-sum-positive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'markov/nnrat-kernel-compose :finite-markov-kernel-composition-positive-support composition/kernel-compose-spec) (support/extend-with :finite-markov-kernel-composition-positive theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-kernel-composition-positive))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
