(ns rainbow.math.finite.signed-argmax-nonexpansive
  "Additive nonexpansiveness of runtime-length finite signed-rational argmax.

  If every declared action satisfies f(a) <= g(a) + epsilon, the maximum
  selected by the executable signed argmax satisfies the same upper bound.
  Supplying both pointwise directions yields the usual two-sided additive
  epsilon certificate.  Scores and epsilon are arbitrary exact signed
  rationals; carrier finiteness and fallback membership are explicit.

  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.signed-argmax :as argmax]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.order-monotone :as monotone]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- source-membership [element source value]
  (app (function/const* 'finset-data/to-set [U]) element source value))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- finite-argmax [element actions fallback score]
  (app (function/const* 'decision/finite-signed-argmax [U])
       element actions fallback score))
(defn- maximum-value [element actions fallback score]
  (app score (finite-argmax element actions fallback score)))

(def finite-argmax-additive-upper-bound-spec
  (let [left-maximum (maximum-value 'A 'actions 'fallback 'left)
        right-maximum (maximum-value 'A 'actions 'fallback 'right)]
    {:name 'decision/finite-signed-argmax-additive-upper-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['actions (exact-finset-of 'A)]
       ['fallback 'A]
       ['fallback-member (source-membership 'A 'actions 'fallback)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]
       ['epsilon signed]
       ['pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership 'A 'actions 'candidate)]]
         (at-most (app 'left 'candidate)
                  (add (app 'right 'candidate) 'epsilon)))]]
      (at-most left-maximum (add right-maximum 'epsilon)))
     :value
     (function/lam
      [['A type-u]
       ['actions (exact-finset-of 'A)]
       ['fallback 'A]
       ['fallback-member (source-membership 'A 'actions 'fallback)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]
       ['epsilon signed]
       ['pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership 'A 'actions 'candidate)]]
         (at-most (app 'left 'candidate)
                  (add (app 'right 'candidate) 'epsilon)))]]
      (let [left-selected (finite-argmax 'A 'actions 'fallback 'left)
            right-selected (finite-argmax 'A 'actions 'fallback 'right)
            left-selected-member
            (app
             (function/const*
              'decision/finite-signed-argmax-is-member [U])
             'A 'actions 'fallback 'left 'fallback-member)
            selected-pointwise
            (app 'pointwise left-selected left-selected-member)
            right-dominates
            (app
             (function/const*
              'decision/finite-signed-argmax-dominates [U])
             'A 'actions 'fallback 'right
             left-selected left-selected-member)
            padded-dominance
            (app
             (function/const* 'signed/add-right-monotone [])
             (app 'right left-selected)
             (app 'right right-selected)
             'epsilon right-dominates)]
        (app
         (function/const* 'signed/at-most-transitive [])
         left-maximum
         (add (app 'right left-selected) 'epsilon)
         (add right-maximum 'epsilon)
         selected-pointwise padded-dominance)))}))

(def finite-argmax-additively-nonexpansive-spec
  (let [left-maximum (maximum-value 'A 'actions 'fallback 'left)
        right-maximum (maximum-value 'A 'actions 'fallback 'right)
        left-to-right
        (at-most left-maximum (add right-maximum 'epsilon))
        right-to-left
        (at-most right-maximum (add left-maximum 'epsilon))]
    {:name 'decision/finite-signed-argmax-additively-nonexpansive
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['actions (exact-finset-of 'A)]
       ['fallback 'A]
       ['fallback-member (source-membership 'A 'actions 'fallback)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership 'A 'actions 'candidate)]]
         (at-most (app 'left 'candidate)
                  (add (app 'right 'candidate) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership 'A 'actions 'candidate)]]
         (at-most (app 'right 'candidate)
                  (add (app 'left 'candidate) 'epsilon)))]]
      (proposition/conjunction left-to-right right-to-left))
     :value
     (function/lam
      [['A type-u]
       ['actions (exact-finset-of 'A)]
       ['fallback 'A]
       ['fallback-member (source-membership 'A 'actions 'fallback)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership 'A 'actions 'candidate)]]
         (at-most (app 'left 'candidate)
                  (add (app 'right 'candidate) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership 'A 'actions 'candidate)]]
         (at-most (app 'right 'candidate)
                  (add (app 'left 'candidate) 'epsilon)))]]
      (app
       (function/const* 'proposition/conjoin [])
       left-to-right right-to-left
       (app
        (function/const*
         'decision/finite-signed-argmax-additive-upper-bound [U])
        'A 'actions 'fallback 'fallback-member
        'left 'right 'epsilon 'left-pointwise)
       (app
        (function/const*
         'decision/finite-signed-argmax-additive-upper-bound [U])
        'A 'actions 'fallback 'fallback-member
        'right 'left 'epsilon 'right-pointwise)))}))

(def definition-specs [])
(def theorem-specs
  [finite-argmax-additive-upper-bound-spec
   finite-argmax-additively-nonexpansive-spec])

(defn- extend-add-right-monotone-if-missing [env]
  (if (environment/resolve-id env 'signed/add-right-monotone)
    env
    (support/extend-with env :signed-order-monotone
                         [monotone/add-right-monotone-spec])))

(defn extend-environment [env]
  (-> env
      argmax/extend-environment
      extend-add-right-monotone-if-missing
      (support/extend-with :finite-signed-argmax-nonexpansive theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
