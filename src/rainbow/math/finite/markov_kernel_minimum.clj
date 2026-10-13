(ns rainbow.math.finite.markov-kernel-minimum
  "A certified global minimum entry of a finite exact-rational kernel.

  Nested finite argmins first select a minimum target in each source row, then
  select a source whose row minimum is globally smallest.  Explicit anchor
  states make the construction total; when those anchors belong to the finite
  carrier, both selected indices belong as well.  Subsequent theorems expose
  positivity and the global lower-bound property for Markov minorization.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.rational-argmin :as argmin]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.positive :as positive]
            [rainbow.math.logic.proposition :as proposition]))

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
(defn- source-member [element states value]
  (membership element (enumeration element states) value))
(defn- finite-argmin [element states initial score]
  (app (function/const* 'decision/finite-nnrat-argmin [U])
       element states initial score))
(defn- row-argmin
  [element states kernel initial-target source]
  (app (function/const* 'markov/nnrat-kernel-row-argmin [U])
       element states kernel initial-target source))
(defn- source-argmin
  [element states kernel initial-source initial-target]
  (app (function/const* 'markov/nnrat-kernel-argmin-source [U])
       element states kernel initial-source initial-target))
(defn- kernel-minimum
  [element states kernel initial-source initial-target]
  (app (function/const* 'markov/nnrat-kernel-minimum [U])
       element states kernel initial-source initial-target))
(defn- positive-rational [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- at-most [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- at-most-transitive [left middle right first second]
  (app (function/const* 'nnrat/at-most-transitive [])
       left middle right first second))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def kernel-row-argmin-spec
  {:name 'markov/nnrat-kernel-row-argmin
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-target 'S]]
    (function/arrow 'S 'S))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-target 'S]
     ['source 'S]]
    (finite-argmin
     'S 'states 'initial-target (app 'kernel 'source)))})

(def kernel-argmin-source-spec
  {:name 'markov/nnrat-kernel-argmin-source
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S 'S 'S))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S]
     ['initial-target 'S]]
    (finite-argmin
     'S 'states 'initial-source
     (function/lam
      [['source 'S]]
      (app
       'kernel 'source
       (row-argmin
        'S 'states 'kernel 'initial-target 'source)))))})

(def kernel-minimum-spec
  {:name 'markov/nnrat-kernel-minimum
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S]
     ['initial-target 'S]]
    (let [selected-source
          (source-argmin
           'S 'states 'kernel 'initial-source 'initial-target)
          selected-target
          (row-argmin
           'S 'states 'kernel 'initial-target selected-source)]
      (app 'kernel selected-source selected-target)))})

(def kernel-row-argmin-member-spec
  {:name 'markov/nnrat-kernel-row-argmin-member
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-target 'S]
     ['initial-target-member
      (source-member 'S 'states 'initial-target)]
     ['source 'S]]
    (source-member
     'S 'states
     (row-argmin
      'S 'states 'kernel 'initial-target 'source)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-target 'S]
     ['initial-target-member
      (source-member 'S 'states 'initial-target)]
     ['source 'S]]
    (app
     (function/const* 'decision/finite-nnrat-argmin-is-member [U])
     'S 'states 'initial-target (app 'kernel 'source)
     'initial-target-member))})

(def kernel-argmin-source-member-spec
  {:name 'markov/nnrat-kernel-argmin-source-member
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S]
     ['initial-target 'S]
     ['initial-source-member
      (source-member 'S 'states 'initial-source)]]
    (source-member
     'S 'states
     (source-argmin
      'S 'states 'kernel 'initial-source 'initial-target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S]
     ['initial-target 'S]
     ['initial-source-member
      (source-member 'S 'states 'initial-source)]]
    (app
     (function/const* 'decision/finite-nnrat-argmin-is-member [U])
     'S 'states 'initial-source
     (function/lam
      [['source 'S]]
      (app
       'kernel 'source
       (row-argmin
        'S 'states 'kernel 'initial-target 'source)))
     'initial-source-member))})

(def kernel-minimum-positive-spec
  {:name 'markov/nnrat-kernel-minimum-positive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S] ['initial-target 'S]
     ['initial-source-member
      (source-member 'S 'states 'initial-source)]
     ['initial-target-member
      (source-member 'S 'states 'initial-target)]
     ['listed-positive
      (function/forall
       [['source 'S] ['target 'S]
        ['source-in-carrier
         (source-member 'S 'states 'source)]
        ['target-in-carrier
         (source-member 'S 'states 'target)]]
       (positive-rational (app 'kernel 'source 'target)))]]
    (positive-rational
     (kernel-minimum
      'S 'states 'kernel 'initial-source 'initial-target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S] ['initial-target 'S]
     ['initial-source-member
      (source-member 'S 'states 'initial-source)]
     ['initial-target-member
      (source-member 'S 'states 'initial-target)]
     ['listed-positive
      (function/forall
       [['source 'S] ['target 'S]
        ['source-in-carrier
         (source-member 'S 'states 'source)]
        ['target-in-carrier
         (source-member 'S 'states 'target)]]
       (positive-rational (app 'kernel 'source 'target)))]]
    (let [selected-source
          (source-argmin
           'S 'states 'kernel 'initial-source 'initial-target)
          selected-target
          (row-argmin
           'S 'states 'kernel 'initial-target selected-source)
          selected-source-member
          (app
           (function/const*
            'markov/nnrat-kernel-argmin-source-member [U])
           'S 'states 'kernel 'initial-source 'initial-target
           'initial-source-member)
          selected-target-member
          (app
           (function/const*
            'markov/nnrat-kernel-row-argmin-member [U])
           'S 'states 'kernel 'initial-target
           'initial-target-member selected-source)]
      (app
       'listed-positive selected-source selected-target
       selected-source-member selected-target-member)))})

(def kernel-minimum-bounds-entry-spec
  {:name 'markov/nnrat-kernel-minimum-bounds-entry
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S] ['initial-target 'S]
     ['source 'S] ['target 'S]
     ['source-in-carrier
      (source-member 'S 'states 'source)]
     ['target-in-carrier
      (source-member 'S 'states 'target)]]
    (at-most
     (kernel-minimum
      'S 'states 'kernel 'initial-source 'initial-target)
     (app 'kernel 'source 'target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S] ['initial-target 'S]
     ['source 'S] ['target 'S]
     ['source-in-carrier
      (source-member 'S 'states 'source)]
     ['target-in-carrier
      (source-member 'S 'states 'target)]]
    (let [row-score
          (function/lam
           [['candidate-source 'S]]
           (app
            'kernel 'candidate-source
            (row-argmin
             'S 'states 'kernel 'initial-target 'candidate-source)))
          selected-source
          (source-argmin
           'S 'states 'kernel 'initial-source 'initial-target)
          candidate-row-minimum
          (app
           'kernel 'source
           (row-argmin
            'S 'states 'kernel 'initial-target 'source))
          global-bound
          (app
           (function/const*
            'decision/finite-nnrat-argmin-dominates [U])
           'S 'states 'initial-source row-score
           'source 'source-in-carrier)
          row-bound
          (app
           (function/const*
            'decision/finite-nnrat-argmin-dominates [U])
           'S 'states 'initial-target (app 'kernel 'source)
           'target 'target-in-carrier)]
      (at-most-transitive
       (kernel-minimum
        'S 'states 'kernel 'initial-source 'initial-target)
       candidate-row-minimum
       (app 'kernel 'source 'target)
       global-bound row-bound)))})

(def kernel-minimum-positive-lower-bound-spec
  {:name 'markov/nnrat-kernel-minimum-positive-lower-bound
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S] ['initial-target 'S]
     ['initial-source-member
      (source-member 'S 'states 'initial-source)]
     ['initial-target-member
      (source-member 'S 'states 'initial-target)]
     ['listed-positive
      (function/forall
       [['source 'S] ['target 'S]
        ['source-in-carrier
         (source-member 'S 'states 'source)]
        ['target-in-carrier
         (source-member 'S 'states 'target)]]
       (positive-rational (app 'kernel 'source 'target)))]]
    (proposition/conjunction
     (positive-rational
      (kernel-minimum
       'S 'states 'kernel 'initial-source 'initial-target))
     (function/forall
      [['source 'S] ['target 'S]
       ['source-in-carrier
        (source-member 'S 'states 'source)]
       ['target-in-carrier
        (source-member 'S 'states 'target)]]
      (at-most
       (kernel-minimum
        'S 'states 'kernel 'initial-source 'initial-target)
       (app 'kernel 'source 'target)))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['initial-source 'S] ['initial-target 'S]
     ['initial-source-member
      (source-member 'S 'states 'initial-source)]
     ['initial-target-member
      (source-member 'S 'states 'initial-target)]
     ['listed-positive
      (function/forall
       [['source 'S] ['target 'S]
        ['source-in-carrier
         (source-member 'S 'states 'source)]
        ['target-in-carrier
         (source-member 'S 'states 'target)]]
       (positive-rational (app 'kernel 'source 'target)))]]
    (let [minimum-value
          (kernel-minimum
           'S 'states 'kernel 'initial-source 'initial-target)
          minimum-positive
          (app
           (function/const* 'markov/nnrat-kernel-minimum-positive [U])
           'S 'states 'kernel 'initial-source 'initial-target
           'initial-source-member 'initial-target-member
           'listed-positive)
          minimum-bounds
          (function/lam
           [['source 'S] ['target 'S]
            ['source-in-carrier
             (source-member 'S 'states 'source)]
            ['target-in-carrier
             (source-member 'S 'states 'target)]]
           (app
            (function/const*
             'markov/nnrat-kernel-minimum-bounds-entry [U])
            'S 'states 'kernel 'initial-source 'initial-target
            'source 'target
            'source-in-carrier 'target-in-carrier))]
      (conjoin
       (positive-rational minimum-value)
       (function/forall
        [['source 'S] ['target 'S]
         ['source-in-carrier
          (source-member 'S 'states 'source)]
         ['target-in-carrier
          (source-member 'S 'states 'target)]]
        (at-most minimum-value (app 'kernel 'source 'target)))
       minimum-positive minimum-bounds)))})

(def definition-specs
  [kernel-row-argmin-spec kernel-argmin-source-spec kernel-minimum-spec])
(def theorem-specs
  [kernel-row-argmin-member-spec kernel-argmin-source-member-spec
   kernel-minimum-positive-spec kernel-minimum-bounds-entry-spec
   kernel-minimum-positive-lower-bound-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.rational-argmin rainbow.math.rational.nnrat.positive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-kernel-minimum (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-kernel-minimum))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
