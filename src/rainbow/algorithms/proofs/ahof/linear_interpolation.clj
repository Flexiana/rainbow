(ns rainbow.algorithms.proofs.ahof.linear-interpolation
  "AHoF D27 Linear Interpolation over exact rationals: interpolate between two values
  a and b with convex weights w0, w1 (summing to one),

      lerp a b w0 w1 = w0 * a + w1 * b.

  Interpolating between 1/2 and 3/4: the midpoint (weights 1/2, 1/2) is 5/8; the left
  endpoint (weights 1, 0) is 1/2; the right endpoint (weights 0, 1) is 3/4. Values are
  proved by cross-product equivalence. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.linear-interpolation`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator denominator-predecessor))
(def half (make-rational (data-nat 1) (data-nat 1)))            ; 1/2
(def three-quarters (make-rational (data-nat 3) (data-nat 3)))  ; 3/4
(def five-eighths (make-rational (data-nat 5) (data-nat 7)))    ; 5/8

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- lerp [a b w0 w1]
  (function/app (function/const* 'interp/lerp []) a b w0 w1))

;; Definitions --------------------------------------------------------------

(def lerp-spec
  {:name 'interp/lerp :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat] ['w0 nnrat] ['w1 nnrat]]
                        (nnrat-add (nnrat-multiply 'w0 'a)
                                   (nnrat-multiply 'w1 'b)))})

(def midpoint-spec
  {:name 'interp/midpoint :kind :definition :universes [] :type nnrat
   :value (lerp half three-quarters half half)})
(def left-endpoint-spec
  {:name 'interp/left-endpoint :kind :definition :universes [] :type nnrat
   :value (lerp half three-quarters nnrat-one nnrat-zero)})
(def right-endpoint-spec
  {:name 'interp/right-endpoint :kind :definition :universes [] :type nnrat
   :value (lerp half three-quarters nnrat-zero nnrat-one)})

(def definition-specs
  [lerp-spec midpoint-spec left-endpoint-spec right-endpoint-spec])

;; Theorems -----------------------------------------------------------------

(def lerp-unfold-spec
  {:name 'interp/lerp-unfold :universes []
   :type (function/forall [['a nnrat] ['b nnrat] ['w0 nnrat] ['w1 nnrat]]
                          (equality nnrat (lerp 'a 'b 'w0 'w1)
                                    (nnrat-add (nnrat-multiply 'w0 'a)
                                               (nnrat-multiply 'w1 'b))))
   :value (function/lam [['a nnrat] ['b nnrat] ['w0 nnrat] ['w1 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (lerp 'a 'b 'w0 'w1)))})

;; The midpoint between 1/2 and 3/4 is 5/8.
(def midpoint-is-five-eighths-spec
  {:name 'interp/midpoint-is-five-eighths :universes []
   :type (nnrat-equivalent (function/const* 'interp/midpoint []) five-eighths)
   :value (equivalent-cross (function/const* 'interp/midpoint []) five-eighths)})

;; The left endpoint (weight 1 on a) returns a = 1/2.
(def left-endpoint-is-a-spec
  {:name 'interp/left-endpoint-is-a :universes []
   :type (nnrat-equivalent (function/const* 'interp/left-endpoint []) half)
   :value (equivalent-cross (function/const* 'interp/left-endpoint []) half)})

;; The right endpoint (weight 1 on b) returns b = 3/4.
(def right-endpoint-is-b-spec
  {:name 'interp/right-endpoint-is-b :universes []
   :type (nnrat-equivalent (function/const* 'interp/right-endpoint []) three-quarters)
   :value (equivalent-cross (function/const* 'interp/right-endpoint []) three-quarters)})

(def linear-interpolation-spec
  (let [mid-law (:type midpoint-is-five-eighths-spec)
        left-law (:type left-endpoint-is-a-spec)]
    {:name 'interp/linear-interpolation :universes []
     :type (proposition/conjunction mid-law left-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      mid-law left-law
      (function/const* 'interp/midpoint-is-five-eighths [])
      (function/const* 'interp/left-endpoint-is-a []))}))

(def theorem-specs
  [lerp-unfold-spec midpoint-is-five-eighths-spec left-endpoint-is-a-spec
   right-endpoint-is-b-spec linear-interpolation-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF linear-interpolation expression failed elaboration"
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
          :rainbow/provenance {:origin :native
                               :producer :ahof-d27-linear-interpolation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF linear-interpolation declaration rejected"
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
