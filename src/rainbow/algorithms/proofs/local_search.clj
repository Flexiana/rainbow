(ns rainbow.algorithms.proofs.local-search
  "Bounded local (hill-climbing) search over a finite candidate set with exact
  rational objectives. A best-neighbor step delegates to the proven finite
  rational argmax: it picks the candidate maximizing the objective, keeping the
  current point as the fallback. Because the current point is itself a candidate,
  each step never decreases the objective -- the hill-climbing guarantee. The
  candidate/objective pair is a pluggable strategy (AHoF D40 DELEGATE)."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- succ [value]
  (function/app (function/const* 'data/succ []) value))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [U])
                element source value))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; Equality of Theta values: Theta : Sort (succ u), so the Eq level is succ u.
(defn- theta-equality [left right]
  (function/equality data-u 'Theta left right))

(defn- argmax [candidates current evaluate]
  (function/app (function/const* 'decision/finite-nnrat-argmax [U])
                'Theta candidates current evaluate))

(defn- best-neighbor [candidates current evaluate]
  (function/app (function/const* 'search/nnrat-best-neighbor [U])
                'Theta candidates current evaluate))

(defn- hill-climb [candidates evaluate steps initial]
  (function/app (function/const* 'search/nnrat-hill-climb [U])
                'Theta candidates evaluate steps initial))

;; Definitions --------------------------------------------------------------

(def best-neighbor-spec
  {:name 'search/nnrat-best-neighbor
   :kind :definition :universes ['u]
   :type (function/forall
          [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
           ['current 'Theta] ['evaluate (function/arrow 'Theta nnrat)]]
          'Theta)
   :value (function/lam
           [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
            ['current 'Theta] ['evaluate (function/arrow 'Theta nnrat)]]
           (argmax 'candidates 'current 'evaluate))})

(def hill-climb-spec
  {:name 'search/nnrat-hill-climb
   :kind :definition :universes ['u]
   :type (function/forall
          [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
           ['evaluate (function/arrow 'Theta nnrat)]]
          (function/arrow nat 'Theta 'Theta))
   :value (function/lam
           [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
            ['evaluate (function/arrow 'Theta nnrat)]
            ['steps nat] ['initial 'Theta]]
           (function/app
            (function/const* 'data/Nat.rec [data-u])
            (function/lam [['ignored nat]] 'Theta)
            'initial
            (function/lam
             [['step-index nat] ['previous 'Theta]]
             (best-neighbor 'candidates 'previous 'evaluate))
            'steps))})

(def definition-specs [best-neighbor-spec hill-climb-spec])

;; Theorems -----------------------------------------------------------------

(def best-neighbor-is-candidate-spec
  {:name 'search/nnrat-best-neighbor-is-candidate
   :universes ['u]
   :type (function/forall
          [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
           ['current 'Theta] ['evaluate (function/arrow 'Theta nnrat)]
           ['current-member (source-membership 'Theta 'candidates 'current)]]
          (source-membership 'Theta 'candidates
                             (best-neighbor 'candidates 'current 'evaluate)))
   :value (function/lam
           [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
            ['current 'Theta] ['evaluate (function/arrow 'Theta nnrat)]
            ['current-member (source-membership 'Theta 'candidates 'current)]]
           (function/app
            (function/const* 'decision/finite-nnrat-argmax-is-member [U])
            'Theta 'candidates 'current 'evaluate 'current-member))})

(def best-neighbor-improves-spec
  {:name 'search/nnrat-best-neighbor-improves
   :universes ['u]
   :type (function/forall
          [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
           ['current 'Theta] ['evaluate (function/arrow 'Theta nnrat)]
           ['current-member (source-membership 'Theta 'candidates 'current)]]
          (at-most (function/app 'evaluate 'current)
                   (function/app 'evaluate
                                 (best-neighbor 'candidates 'current
                                                'evaluate))))
   :value (function/lam
           [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
            ['current 'Theta] ['evaluate (function/arrow 'Theta nnrat)]
            ['current-member (source-membership 'Theta 'candidates 'current)]]
           (function/app
            (function/const* 'decision/finite-nnrat-argmax-dominates [U])
            'Theta 'candidates 'current 'evaluate 'current 'current-member))})

(def hill-climb-zero-spec
  {:name 'search/nnrat-hill-climb-zero
   :universes ['u]
   :type (function/forall
          [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
           ['evaluate (function/arrow 'Theta nnrat)] ['initial 'Theta]]
          (theta-equality
           (hill-climb 'candidates 'evaluate
                       (function/const* 'data/zero []) 'initial)
           'initial))
   :value (function/lam
           [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
            ['evaluate (function/arrow 'Theta nnrat)] ['initial 'Theta]]
           (function/app (function/const* 'equality/reflexive [data-u])
                         'Theta 'initial))})

(def hill-climb-successor-spec
  (let [step (function/lam
              [['step-index nat] ['previous 'Theta]]
              (best-neighbor 'candidates 'previous 'evaluate))
        previous (hill-climb 'candidates 'evaluate 'steps 'initial)
        next (hill-climb 'candidates 'evaluate (succ 'steps) 'initial)]
    {:name 'search/nnrat-hill-climb-successor
     :universes ['u]
     :type (function/forall
            [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
             ['evaluate (function/arrow 'Theta nnrat)]
             ['steps nat] ['initial 'Theta]]
            (theta-equality next (function/app step 'steps previous)))
     :value (function/lam
             [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
              ['evaluate (function/arrow 'Theta nnrat)]
              ['steps nat] ['initial 'Theta]]
             (function/app
              (function/const* 'nat/recursor-successor-constant [U])
              'Theta 'initial step 'steps))}))

(def best-neighbor-transfer-spec
  (let [improves
        (fn [current member]
          [(at-most (function/app 'evaluate current)
                    (function/app 'evaluate
                                  (best-neighbor 'candidates current
                                                 'evaluate)))
           (function/app
            (function/const* 'decision/finite-nnrat-argmax-dominates [U])
            'Theta 'candidates current 'evaluate current member)])]
    {:name 'search/nnrat-best-neighbor-transfer
     :universes ['u]
     :type (function/forall
            [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
             ['evaluate (function/arrow 'Theta nnrat)]
             ['left 'Theta]
             ['left-member (source-membership 'Theta 'candidates 'left)]
             ['right 'Theta]
             ['right-member (source-membership 'Theta 'candidates 'right)]]
            (proposition/conjunction
             (first (improves 'left 'left-member))
             (first (improves 'right 'right-member))))
     :value (function/lam
             [['Theta type-u] ['candidates (exact-finset-of 'Theta)]
              ['evaluate (function/arrow 'Theta nnrat)]
              ['left 'Theta]
              ['left-member (source-membership 'Theta 'candidates 'left)]
              ['right 'Theta]
              ['right-member (source-membership 'Theta 'candidates 'right)]]
             (function/app
              (function/const* 'proposition/conjoin [])
              (first (improves 'left 'left-member))
              (first (improves 'right 'right-member))
              (second (improves 'left 'left-member))
              (second (improves 'right 'right-member))))}))

(def theorem-specs
  [best-neighbor-is-candidate-spec best-neighbor-improves-spec
   hill-climb-zero-spec hill-climb-successor-spec
   best-neighbor-transfer-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Local-search expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance {:origin :native :producer :local-search}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Local-search declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment
          (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
