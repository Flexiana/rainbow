(ns rainbow.math.finite.markov-kernel-algebra
  "Congruence, associativity, and observable action for exact finite kernels.

  Kernel composition respects pointwise equivalence in both arguments and is
  associative up to NNRAT equivalence.  Its backward action on observables
  composes in the same order: (K ; L)f ~ K(Lf).  Native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.math.finite.markov-expectation-tower :as tower]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- kernel-step [element states kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass target))
(defn- kernel-compose [element states first-kernel second-kernel source target]
  (app (function/const* 'markov/nnrat-kernel-compose [U])
       element states first-kernel second-kernel source target))
(defn- kernel-observable [element states kernel observable source]
  (app (function/const* 'markov/nnrat-kernel-observable [U])
       element states kernel observable source))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))

(def kernel-compose-respects-first-spec
  {:name 'markov/nnrat-kernel-compose-respects-first-equivalence
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['left-first (function/arrow 'S 'S nnrat)]
     ['right-first (function/arrow 'S 'S nnrat)]
     ['same-first
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-first 'source 'target)
            (app 'right-first 'source 'target)))]
     ['second-kernel (function/arrow 'S 'S nnrat)]]
    (function/forall
     [['source 'S] ['target 'S]]
     (req
      (kernel-compose
       'S 'states 'left-first 'second-kernel 'source 'target)
      (kernel-compose
       'S 'states 'right-first 'second-kernel 'source 'target))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['left-first (function/arrow 'S 'S nnrat)]
     ['right-first (function/arrow 'S 'S nnrat)]
     ['same-first
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-first 'source 'target)
            (app 'right-first 'source 'target)))]
     ['second-kernel (function/arrow 'S 'S nnrat)]]
    (function/lam
     [['source 'S] ['target 'S]]
     (app
      (function/const*
       'markov/nnrat-kernel-step-respects-mass-equivalence [U])
      'S 'states 'second-kernel
      (app 'left-first 'source) (app 'right-first 'source)
      (function/lam
       [['middle 'S]]
       (app 'same-first 'source 'middle))
      'target)))})

(def kernel-compose-respects-second-spec
  {:name 'markov/nnrat-kernel-compose-respects-second-equivalence
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['left-second (function/arrow 'S 'S nnrat)]
     ['right-second (function/arrow 'S 'S nnrat)]
     ['same-second
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-second 'source 'target)
            (app 'right-second 'source 'target)))]]
    (function/forall
     [['source 'S] ['target 'S]]
     (req
      (kernel-compose
       'S 'states 'first-kernel 'left-second 'source 'target)
      (kernel-compose
       'S 'states 'first-kernel 'right-second 'source 'target))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['left-second (function/arrow 'S 'S nnrat)]
     ['right-second (function/arrow 'S 'S nnrat)]
     ['same-second
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-second 'source 'target)
            (app 'right-second 'source 'target)))]]
    (function/lam
     [['source 'S] ['target 'S]]
     (app
      (function/const*
       'markov/nnrat-kernel-step-respects-kernel-equivalence [U])
      'S 'states 'left-second 'right-second 'same-second
      (app 'first-kernel 'source) 'target)))})

(def kernel-compose-respects-spec
  {:name 'markov/nnrat-kernel-compose-respects-equivalence
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['left-first (function/arrow 'S 'S nnrat)]
     ['right-first (function/arrow 'S 'S nnrat)]
     ['same-first
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-first 'source 'target)
            (app 'right-first 'source 'target)))]
     ['left-second (function/arrow 'S 'S nnrat)]
     ['right-second (function/arrow 'S 'S nnrat)]
     ['same-second
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-second 'source 'target)
            (app 'right-second 'source 'target)))]]
    (function/forall
     [['source 'S] ['target 'S]]
     (req
      (kernel-compose
       'S 'states 'left-first 'left-second 'source 'target)
      (kernel-compose
       'S 'states 'right-first 'right-second 'source 'target))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['left-first (function/arrow 'S 'S nnrat)]
     ['right-first (function/arrow 'S 'S nnrat)]
     ['same-first
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-first 'source 'target)
            (app 'right-first 'source 'target)))]
     ['left-second (function/arrow 'S 'S nnrat)]
     ['right-second (function/arrow 'S 'S nnrat)]
     ['same-second
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-second 'source 'target)
            (app 'right-second 'source 'target)))]]
    (function/lam
     [['source 'S] ['target 'S]]
     (let [left
           (kernel-compose
            'S 'states 'left-first 'left-second 'source 'target)
           middle
           (kernel-compose
            'S 'states 'right-first 'left-second 'source 'target)
           right
           (kernel-compose
            'S 'states 'right-first 'right-second 'source 'target)
           first-proof
           (app
            (function/const*
             'markov/nnrat-kernel-compose-respects-first-equivalence [U])
            'S 'states 'left-first 'right-first 'same-first
            'left-second 'source 'target)
           second-proof
           (app
            (function/const*
             'markov/nnrat-kernel-compose-respects-second-equivalence [U])
            'S 'states 'right-first 'left-second 'right-second
            'same-second 'source 'target)]
       (equivalent-transitive
        left middle right first-proof second-proof))))})

(def kernel-compose-associative-spec
  {:name 'markov/nnrat-kernel-compose-associative
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['third-kernel (function/arrow 'S 'S nnrat)]]
    (function/forall
     [['source 'S] ['target 'S]]
     (req
      (kernel-compose
       'S 'states
       (function/lam
        [['left 'S] ['right 'S]]
        (kernel-compose
         'S 'states 'first-kernel 'second-kernel 'left 'right))
       'third-kernel 'source 'target)
      (kernel-compose
       'S 'states 'first-kernel
       (function/lam
        [['left 'S] ['right 'S]]
        (kernel-compose
         'S 'states 'second-kernel 'third-kernel 'left 'right))
       'source 'target))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['third-kernel (function/arrow 'S 'S nnrat)]]
    (function/lam
     [['source 'S] ['target 'S]]
     (let [right
           (kernel-compose
            'S 'states 'first-kernel
            (function/lam
             [['left 'S] ['destination 'S]]
             (kernel-compose
              'S 'states 'second-kernel 'third-kernel
              'left 'destination))
            'source 'target)
           left
           (kernel-compose
            'S 'states
            (function/lam
             [['left-source 'S] ['middle 'S]]
             (kernel-compose
              'S 'states 'first-kernel 'second-kernel
              'left-source 'middle))
            'third-kernel 'source 'target)
           forward
           (app
            (function/const* 'markov/nnrat-kernel-step-compose [U])
            'S 'states 'second-kernel 'third-kernel
            (app 'first-kernel 'source) 'target)]
       (equivalent-symmetric right left forward))))})

(def kernel-observable-compose-spec
  {:name 'markov/nnrat-kernel-observable-compose
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['observable (function/arrow 'S nnrat)]]
    (function/forall
     [['source 'S]]
     (req
      (kernel-observable
       'S 'states
       (function/lam
        [['left 'S] ['right 'S]]
        (kernel-compose
         'S 'states 'first-kernel 'second-kernel 'left 'right))
       'observable 'source)
      (kernel-observable
       'S 'states 'first-kernel
       (function/lam
        [['middle 'S]]
        (kernel-observable
         'S 'states 'second-kernel 'observable 'middle))
       'source))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['observable (function/arrow 'S nnrat)]]
    (function/lam
     [['source 'S]]
     (app
      (function/const* 'markov/nnrat-expectation-after-kernel-step [U])
      'S 'states 'second-kernel (app 'first-kernel 'source)
      'observable)))})

(def definition-specs [])

(def theorem-specs
  [kernel-compose-respects-first-spec
   kernel-compose-respects-second-spec
   kernel-compose-respects-spec
   kernel-compose-associative-spec
   kernel-observable-compose-spec])

(defn extend-environment [env]
  (-> env
      tower/extend-environment
      (support/extend-with
       :finite-markov-kernel-algebra theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
