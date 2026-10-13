(ns rainbow.algorithms.proofs.ahof.pattern-search
  "AHoF O35 worked generalized pattern search over exact rationals, minimizing
  f(x) = x^2 from x = 2 with step 1. The poll evaluates the two candidates x + 1 = 3
  (objective 9) and x - 1 = 1 (objective 1); the smaller objective is 1, so the
  poll picks the point 1. Since the polled objective 1 improves on the current
  objective f(2) = 4, the move is accepted to 1 -- a derivative-free step using
  only objective comparisons. The selections are proved by reflexivity of the
  decided comparisons.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.pattern-search`
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
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def one-value (make-rational (data-nat 1) (data-nat 0)))
(def four (make-rational (data-nat 4) (data-nat 0)))
(def nine (make-rational (data-nat 9) (data-nat 0)))
(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))
(defn- signed-equality [left right]
  (function/equality type-level signed left right))

(defn- poll-better [value-a value-b point-a point-b]
  (function/app (function/const* 'search/poll-better [])
                value-a value-b point-a point-b))
(defn- pattern-move [best-value current-value best-point current-point]
  (function/app (function/const* 'search/pattern-move [])
                best-value current-value best-point current-point))

;; Candidate points x+1 = 3 and x-1 = 1, with objectives 9 and 1; current x = 2
;; with objective 4.
(def forward-point (function/const* 'ahof-o35/forward-point []))
(def backward-point (function/const* 'ahof-o35/backward-point []))
(def current-point (function/const* 'ahof-o35/current-point []))

;; Definitions --------------------------------------------------------------

(def forward-point-spec
  {:name 'ahof-o35/forward-point :kind :definition :universes []
   :type signed :value (from-nnrat (make-rational (data-nat 3) (data-nat 0)))})

(def backward-point-spec
  {:name 'ahof-o35/backward-point :kind :definition :universes []
   :type signed :value (from-nnrat one-value)})

(def current-point-spec
  {:name 'ahof-o35/current-point :kind :definition :universes []
   :type signed :value (from-nnrat (make-rational (data-nat 2) (data-nat 0)))})

;; The polled best of the two candidates: objectives 9 (forward) and 1 (backward).
(def polled-best-spec
  {:name 'ahof-o35/polled-best :kind :definition :universes []
   :type signed
   :value (poll-better nine one-value forward-point backward-point)})

(def definition-specs
  [forward-point-spec backward-point-spec current-point-spec polled-best-spec])

;; Theorems -----------------------------------------------------------------

;; The poll picks the backward point (smaller objective 1).
(def poll-picks-backward-spec
  {:name 'ahof-o35/poll-picks-backward :universes []
   :type (signed-equality
          (function/const* 'ahof-o35/polled-best []) backward-point)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        signed backward-point)})

;; The polled best (objective 1) improves the current (objective 4), so the move
;; goes to the polled best.
(def move-accepts-best-spec
  {:name 'ahof-o35/move-accepts-best :universes []
   :type (signed-equality
          (pattern-move one-value four
                        (function/const* 'ahof-o35/polled-best [])
                        current-point)
          backward-point)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        signed backward-point)})

(def pattern-search-spec
  (let [poll-law (:type poll-picks-backward-spec)
        move-law (:type move-accepts-best-spec)]
    {:name 'ahof-o35/pattern-search :universes []
     :type (proposition/conjunction poll-law move-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      poll-law move-law
      (function/const* 'ahof-o35/poll-picks-backward [])
      (function/const* 'ahof-o35/move-accepts-best []))}))

(def theorem-specs
  [poll-picks-backward-spec move-accepts-best-spec pattern-search-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF pattern-search expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-o35-pattern-search}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF pattern-search declaration rejected"
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
