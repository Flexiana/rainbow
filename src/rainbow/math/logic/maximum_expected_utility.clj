(ns rainbow.math.logic.maximum-expected-utility
  "AHoF D17: finite exact-rational maximum expected utility."
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
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- succ [value] (function/app successor value))
(defn- numeral [value] (nth (iterate succ zero) value))
(def one (numeral 1))
(def two (numeral 2))
(def three (numeral 3))
(def four (numeral 4))
(def ten (numeral 10))

(defn- rational [numerator]
  (function/app (function/const* 'nnrat/make []) numerator zero))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [zero-level]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [zero-level])
                element source))

(defn- membership [element source value]
  (function/app (function/const* 'list/membership [zero-level])
                element source value))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [zero-level])
                element source value))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- map-sum [mapping source]
  (function/app (function/const* 'list/nnrat-map-sum [zero-level])
                nat mapping source))

(defn- expectation [source mass value]
  (function/app
   (function/const* 'probability/nnrat-expectation [zero-level])
   nat source mass value))

(def action-space-spec
  {:name 'ahof-d17/action-space
   :kind :definition :universes []
   :type (exact-finset-of nat)
   :value (function/app (function/const* 'finset-data/range []) three)})

(def outcome-space-spec
  {:name 'ahof-d17/outcome-space
   :kind :definition :universes []
   :type (exact-finset-of nat)
   :value (function/app (function/const* 'finset-data/range []) one)})

(defn- named-nat [name value]
  {:name name :kind :definition :universes [] :type nat :value value})

(def accept-spec (named-nat 'ahof-d17/accept zero))
(def renegotiate-spec (named-nat 'ahof-d17/renegotiate one))
(def decline-spec (named-nat 'ahof-d17/decline two))

(def probability-mass-spec
  {:name 'ahof-d17/probability-mass
   :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (function/lam [['ignored-outcome nat]] nnrat-one)})

(def utility-spec
  {:name 'ahof-d17/utility
   :kind :definition :universes []
   :type (function/arrow nat nat nnrat)
   :value
   (function/lam
    [['action nat] ['ignored-outcome nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nnrat)
     (rational four)
     (function/lam
      [['previous nat] ['ignored-previous-utility nnrat]]
      (function/app
       (function/const* 'data/Nat.rec [type-level])
       (function/lam [['ignored nat]] nnrat)
       (rational ten)
       (function/lam
        [['ignored-previous nat] ['ignored-utility nnrat]]
        nnrat-zero)
       'previous))
     'action))})

(def expected-utility-spec
  {:name 'ahof-d17/expected-utility
   :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value
   (function/lam
    [['action nat]]
    (function/app (function/const* 'ahof-d17/utility []) 'action zero))})

(def finite-expected-utility-spec
  {:name 'ahof-d17/finite-expected-utility
   :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value
   (function/lam
    [['action nat]]
    (expectation
     (function/const* 'ahof-d17/outcome-space [])
     (function/const* 'ahof-d17/probability-mass [])
     (function/lam
      [['outcome nat]]
      (function/app (function/const* 'ahof-d17/utility [])
                    'action 'outcome))))})

(def total-mass-spec
  {:name 'ahof-d17/total-mass
   :kind :definition :universes [] :type nnrat
   :value
   (map-sum
    (function/const* 'ahof-d17/probability-mass [])
    (enumeration nat (function/const* 'ahof-d17/outcome-space [])))})

(def selected-action-spec
  {:name 'ahof-d17/selected-action
   :kind :definition :universes [] :type nat
   :value
   (function/app
    (function/const* 'decision/finite-nnrat-argmax [zero-level])
    nat
    (function/const* 'ahof-d17/action-space [])
    (function/const* 'ahof-d17/accept [])
    (function/const* 'ahof-d17/expected-utility []))})

(def definition-specs
  [action-space-spec outcome-space-spec accept-spec renegotiate-spec
   decline-spec probability-mass-spec utility-spec expected-utility-spec
   finite-expected-utility-spec total-mass-spec selected-action-spec])

(def accept-member-spec
  (let [actions (function/const* 'ahof-d17/action-space [])
        accept (function/const* 'ahof-d17/accept [])]
    {:name 'ahof-d17/accept-is-action
     :universes []
     :type (source-membership nat actions accept)
     :value
     (function/app
      (function/const* 'proposition/right-disjunct [])
      (equality nat accept two)
      (membership nat
                  (function/app
                   (function/const* 'data/cons [type-level])
                   nat one
                   (function/app
                    (function/const* 'data/cons [type-level])
                    nat zero
                    (function/app (function/const* 'data/nil [type-level])
                                  nat)))
                  accept)
      (function/app
       (function/const* 'proposition/right-disjunct [])
       (equality nat accept one)
       (membership nat
                   (function/app
                    (function/const* 'data/cons [type-level])
                    nat zero
                    (function/app (function/const* 'data/nil [type-level])
                                  nat))
                   accept)
       (function/app
        (function/const* 'proposition/left-disjunct [])
        (equality nat accept zero)
        (membership nat
                    (function/app (function/const* 'data/nil [type-level])
                                  nat)
                    accept)
        (function/app (function/const* 'equality/reflexive [type-level])
                      nat zero))))}))

(def probabilities-normalized-spec
  {:name 'ahof-d17/probabilities-normalized
   :universes []
   :type (equivalent (function/const* 'ahof-d17/total-mass []) nnrat-one)
   :value
   (function/app (function/const* 'nnrat/equivalent-reflexive []) nnrat-one)})

(def expected-utility-is-finite-expectation-spec
  (let [direct (function/const* 'ahof-d17/expected-utility [])
        finite (function/const* 'ahof-d17/finite-expected-utility [])
        accept (function/const* 'ahof-d17/accept [])
        renegotiate (function/const* 'ahof-d17/renegotiate [])
        decline (function/const* 'ahof-d17/decline [])
        accept-law (equivalent (function/app direct accept)
                               (function/app finite accept))
        renegotiate-law (equivalent (function/app direct renegotiate)
                                    (function/app finite renegotiate))
        decline-law (equivalent (function/app direct decline)
                                (function/app finite decline))]
    {:name 'ahof-d17/expected-utility-is-finite-expectation
     :universes []
     :type
     (proposition/conjunction
      accept-law (proposition/conjunction renegotiate-law decline-law))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      accept-law (proposition/conjunction renegotiate-law decline-law)
      (function/app (function/const* 'nnrat/equivalent-reflexive [])
                    (rational four))
      (function/app
       (function/const* 'proposition/conjoin [])
       renegotiate-law decline-law
       (function/app (function/const* 'nnrat/equivalent-reflexive [])
                     (rational ten))
       (function/app (function/const* 'nnrat/equivalent-reflexive [])
                     nnrat-zero)))}))

(def selected-is-renegotiate-spec
  {:name 'ahof-d17/selected-is-renegotiate
   :universes []
   :type
   (equality nat
             (function/const* 'ahof-d17/selected-action [])
             (function/const* 'ahof-d17/renegotiate []))
   :value
   (function/app (function/const* 'equality/reflexive [type-level]) nat one)})

(def selected-is-member-spec
  (let [actions (function/const* 'ahof-d17/action-space [])
        selected (function/const* 'ahof-d17/selected-action [])]
    {:name 'ahof-d17/selected-is-member
     :universes []
     :type (source-membership nat actions selected)
     :value
     (function/app
      (function/const* 'decision/finite-nnrat-argmax-is-member [zero-level])
      nat actions
      (function/const* 'ahof-d17/accept [])
      (function/const* 'ahof-d17/expected-utility [])
      (function/const* 'ahof-d17/accept-is-action []))}))

(def selected-dominates-spec
  (let [actions (function/const* 'ahof-d17/action-space [])
        selected (function/const* 'ahof-d17/selected-action [])
        score (function/const* 'ahof-d17/expected-utility [])]
    {:name 'ahof-d17/selected-dominates
     :universes []
     :type
     (function/forall
      [['candidate nat]
       ['member (source-membership nat actions 'candidate)]]
      (at-most (function/app score 'candidate)
               (function/app score selected)))
     :value
     (function/lam
      [['candidate nat]
       ['member (source-membership nat actions 'candidate)]]
      (function/app
       (function/const* 'decision/finite-nnrat-argmax-dominates [zero-level])
       nat actions
       (function/const* 'ahof-d17/accept []) score
       'candidate 'member))}))

(def maximum-expected-utility-spec
  (let [actions (function/const* 'ahof-d17/action-space [])
        selected (function/const* 'ahof-d17/selected-action [])
        score (function/const* 'ahof-d17/expected-utility [])
        normalized
        (equivalent (function/const* 'ahof-d17/total-mass []) nnrat-one)
        selected-correct
        (equality nat selected (function/const* 'ahof-d17/renegotiate []))
        selected-member (source-membership nat actions selected)
        dominant
        (function/forall
         [['candidate nat]
          ['member (source-membership nat actions 'candidate)]]
         (at-most (function/app score 'candidate)
                  (function/app score selected)))]
    {:name 'ahof-d17/maximum-expected-utility
     :universes []
     :type
     (proposition/conjunction
      normalized
      (proposition/conjunction
       selected-correct
       (proposition/conjunction selected-member dominant)))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      normalized
      (proposition/conjunction
       selected-correct
       (proposition/conjunction selected-member dominant))
      (function/const* 'ahof-d17/probabilities-normalized [])
      (function/app
       (function/const* 'proposition/conjoin [])
       selected-correct
       (proposition/conjunction selected-member dominant)
       (function/const* 'ahof-d17/selected-is-renegotiate [])
       (function/app
        (function/const* 'proposition/conjoin [])
        selected-member dominant
        (function/const* 'ahof-d17/selected-is-member [])
        (function/const* 'ahof-d17/selected-dominates []))))}))

(def theorem-specs
  [accept-member-spec probabilities-normalized-spec
   expected-utility-is-finite-expectation-spec
   selected-is-renegotiate-spec selected-is-member-spec
   selected-dominates-spec maximum-expected-utility-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Maximum expected utility expression failed elaboration"
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
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :ahof-d17-maximum-expected-utility}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Maximum expected utility declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.logic.maximum-expected-utility))
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
