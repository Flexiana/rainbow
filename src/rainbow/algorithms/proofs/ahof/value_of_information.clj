(ns rainbow.algorithms.proofs.ahof.value-of-information
  "AHoF D19 worked value of information over signed rationals.

  The value of information is the signed difference EU(with info) - EU(without
  info). With a worked decision problem where informed expected utility is 3/4
  and uninformed is 1/2, the value of information is exactly 1/4, and the worked
  certificates 1/2 <= 3/4 and 1/4 nonnegative are proved. That information never
  reduces expected utility is the classical property of the value of information
  and is not proved here. Signed subtraction is the addition-only Grothendieck
  construction, so no primitive subtraction is needed.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.value-of-information`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))

(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))

(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- nat-add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- nat-equality [left right]
  (function/equality type-level nat left right))

(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- nnrat-at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))

(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))

(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))

(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))

;; A witness proof of `nat/at-most a b` given a + extra = b.
(defn- nat-at-most-witness [a b extra]
  (function/app
   (function/const* 'proposition/witness [type-level])
   nat
   (function/lam [['extra nat]] (nat-equality (nat-add a 'extra) b))
   extra
   (function/app (function/const* 'equality/reflexive [type-level])
                 nat (nat-add a extra))))

;; A proof of `nnrat/at-most left right` via cross multiplication, given the
;; extra witness for the resulting nat inequality.
(defn- nnrat-at-most-cross [left right extra]
  (function/app
   (function/const* 'nnrat/at-most-from-cross [])
   left right
   (nat-at-most-witness
    (multiply-nat (numerator left) (denominator right))
    (multiply-nat (numerator right) (denominator left))
    extra)))

;; A proof of `nnrat/equivalent left right` via cross-product reflexivity.
(defn- nnrat-equivalent-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

(def eu-with-value (make-rational (data-nat 3) (data-nat 3)))    ; 3/4
(def eu-without-value (make-rational (data-nat 1) (data-nat 1)))  ; 1/2
(def eu-quarter (make-rational (data-nat 1) (data-nat 3)))        ; 1/4

(def eu-with (function/const* 'ahof-d19/eu-with-info []))
(def eu-without (function/const* 'ahof-d19/eu-without-info []))
(def value-of-information (function/const* 'ahof-d19/value-of-information []))

;; Definitions --------------------------------------------------------------

(def eu-with-spec
  {:name 'ahof-d19/eu-with-info :kind :definition :universes []
   :type signed :value (from-nnrat eu-with-value)})

(def eu-without-spec
  {:name 'ahof-d19/eu-without-info :kind :definition :universes []
   :type signed :value (from-nnrat eu-without-value)})

(def value-of-information-spec
  {:name 'ahof-d19/value-of-information :kind :definition :universes []
   :type signed
   :value (function/app (function/const* 'signed/subtract [])
                        eu-with eu-without)})

(def definition-specs
  [eu-with-spec eu-without-spec value-of-information-spec])

;; Theorems -----------------------------------------------------------------

(def information-never-hurts-spec
  ;; EU(without info) <= EU(with info): 1/2 <= 3/4 via cross 1*4 <= 3*2 (4+2=6).
  {:name 'ahof-d19/information-never-hurts :universes []
   :type (nnrat-at-most eu-without-value eu-with-value)
   :value (nnrat-at-most-cross eu-without-value eu-with-value (data-nat 2))})

(def voi-equals-quarter-spec
  ;; The value of information equals the signed rational 1/4.
  (let [target (from-nnrat eu-quarter)
        left (nnrat-add (signed-positive value-of-information)
                        (signed-negative target))
        right (nnrat-add (signed-positive target)
                         (signed-negative value-of-information))]
    {:name 'ahof-d19/voi-equals-quarter :universes []
     :type (signed-equivalent value-of-information target)
     :value (nnrat-equivalent-cross left right)}))

(def voi-nonnegative-spec
  ;; The value of information is a nonnegative signed rational: neg <= pos, i.e.
  ;; (0 + 1/2) <= (3/4 + 0) via cross multiplication.
  (let [neg (signed-negative value-of-information)
        pos (signed-positive value-of-information)]
    {:name 'ahof-d19/voi-nonnegative :universes []
     :type (function/app (function/const* 'signed/nonnegative [])
                         value-of-information)
     :value (nnrat-at-most-cross neg pos (data-nat 2))}))

(def value-of-information-package-spec
  (let [never-hurts (:type information-never-hurts-spec)
        equals-quarter (:type voi-equals-quarter-spec)
        nonnegative (:type voi-nonnegative-spec)]
    {:name 'ahof-d19/value-of-information-theorem :universes []
     :type (proposition/conjunction
            never-hurts (proposition/conjunction equals-quarter nonnegative))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      never-hurts (proposition/conjunction equals-quarter nonnegative)
      (function/const* 'ahof-d19/information-never-hurts [])
      (function/app
       (function/const* 'proposition/conjoin [])
       equals-quarter nonnegative
       (function/const* 'ahof-d19/voi-equals-quarter [])
       (function/const* 'ahof-d19/voi-nonnegative [])))}))

(def theorem-specs
  [information-never-hurts-spec voi-equals-quarter-spec voi-nonnegative-spec
   value-of-information-package-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF value-of-information expression failed elaboration"
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
          :rainbow/provenance
          {:origin :native :producer :ahof-d19-value-of-information}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF value-of-information declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.value-of-information))
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
