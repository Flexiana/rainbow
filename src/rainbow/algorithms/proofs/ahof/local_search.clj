(ns rainbow.algorithms.proofs.ahof.local-search
  "AHoF D40 worked bounded local (hill-climbing) policy search.

  Three candidate policies {0,1,2} scored 1/4, 3/4, 1/2 by an exact rational
  objective. From the current policy 0 the best-neighbor step selects policy 1
  (the maximizer), which is admissible and never decreases the objective
  (1/4 <= 3/4). The candidate membership proofs reuse the finite range machinery.

  Scope (measured by the kernel): this module has 5 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.local-search`
  prints this classification."
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
(def nnrat-half (function/const* 'nnrat/half []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))

(defn- succ [value] (function/app (function/const* 'data/succ []) value))

(defn- nat-add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- nat-equality [left right]
  (function/equality type-level nat left right))

(defn- decide-nat-equality [left right]
  (function/app (function/const* 'nat/decide-equality []) left right))

(defn- if-data [condition decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat condition decision then-value else-value))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

;; Reusable proof that `value` (with `value + 1 + extra = upper`) is a member of
;; the finite range {0, ..., upper-1}.
(defn- member-of-range [value upper extra]
  (function/app
   (function/const* 'nat/below-member-range [])
   value upper
   (function/app
    (function/const* 'proposition/witness [type-level])
    nat
    (function/lam
     [['extra nat]]
     (nat-equality (nat-add (succ value) 'extra) upper))
    extra
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (nat-add (succ value) extra)))))

(def candidates (function/const* 'ahof-d40/candidates []))
(def objective (function/const* 'ahof-d40/objective []))

(defn- best-neighbor [current]
  (function/app (function/const* 'search/nnrat-best-neighbor [zero-level])
                nat candidates current objective))

;; Definitions --------------------------------------------------------------

(def candidates-spec
  {:name 'ahof-d40/candidates :kind :definition :universes []
   :type (function/app (function/const* 'finset-data/Finset [zero-level]) nat)
   :value (function/app (function/const* 'finset-data/range []) (data-nat 3))})

(def objective-spec
  {:name 'ahof-d40/objective :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value
   (function/lam
    [['policy nat]]
    (if-data (nat-equality 'policy (data-nat 1))
             (decide-nat-equality 'policy (data-nat 1))
             (make-rational (data-nat 3) (data-nat 3))
             (if-data (nat-equality 'policy (data-nat 2))
                      (decide-nat-equality 'policy (data-nat 2))
                      nnrat-half
                      (make-rational (data-nat 1) (data-nat 3)))))})

(def definition-specs [candidates-spec objective-spec])

;; Theorems -----------------------------------------------------------------

(def best-is-one-spec
  {:name 'ahof-d40/best-is-one :universes []
   :type (nat-equality (best-neighbor (data-nat 0)) (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (best-neighbor (data-nat 0)))})

(def admissible-spec
  {:name 'ahof-d40/admissible :universes []
   :type (function/app (function/const* 'finset-data/to-set [zero-level])
                       nat candidates (best-neighbor (data-nat 0)))
   :value (function/app
           (function/const* 'search/nnrat-best-neighbor-is-candidate
                            [zero-level])
           nat candidates (data-nat 0) objective
           (member-of-range (data-nat 0) (data-nat 3) (data-nat 2)))})

(def improvement-spec
  {:name 'ahof-d40/improvement :universes []
   :type (at-most (function/app objective (data-nat 0))
                  (function/app objective (best-neighbor (data-nat 0))))
   :value (function/app
           (function/const* 'search/nnrat-best-neighbor-improves
                            [zero-level])
           nat candidates (data-nat 0) objective
           (member-of-range (data-nat 0) (data-nat 3) (data-nat 2)))})

(def recurrence-spec
  (let [hill-climb (fn [steps initial]
                     (function/app
                      (function/const* 'search/nnrat-hill-climb [zero-level])
                      nat candidates objective steps initial))
        step (function/lam
              [['step-index nat] ['previous nat]]
              (best-neighbor 'previous))
        base-law (nat-equality
                  (hill-climb (function/const* 'data/zero []) (data-nat 0))
                  (data-nat 0))
        successor-law
        (function/forall
         [['steps nat]]
         (nat-equality (hill-climb (succ 'steps) (data-nat 0))
                       (function/app step 'steps
                                     (hill-climb 'steps (data-nat 0)))))]
    {:name 'ahof-d40/hill-climb-recurrence :universes []
     :type (proposition/conjunction base-law successor-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law successor-law
      (function/app
       (function/const* 'search/nnrat-hill-climb-zero [zero-level])
       nat candidates objective (data-nat 0))
      (function/lam
       [['steps nat]]
       (function/app
        (function/const* 'search/nnrat-hill-climb-successor [zero-level])
        nat candidates objective 'steps (data-nat 0))))}))

(def local-search-spec
  (let [admissible (:type admissible-spec)
        improvement (:type improvement-spec)
        recurrence (:type recurrence-spec)]
    {:name 'ahof-d40/local-search :universes []
     :type (proposition/conjunction
            admissible (proposition/conjunction improvement recurrence))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      admissible (proposition/conjunction improvement recurrence)
      (function/const* 'ahof-d40/admissible [])
      (function/app
       (function/const* 'proposition/conjoin [])
       improvement recurrence
       (function/const* 'ahof-d40/improvement [])
       (function/const* 'ahof-d40/hill-climb-recurrence [])))}))

(def theorem-specs
  [best-is-one-spec admissible-spec improvement-spec recurrence-spec
   local-search-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF local-search expression failed elaboration"
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
          {:origin :native :producer :ahof-d40-local-search}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF local-search declaration rejected"
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
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.local-search))
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
