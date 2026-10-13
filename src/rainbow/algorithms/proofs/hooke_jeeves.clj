(ns rainbow.algorithms.proofs.hooke-jeeves
  "AHoF O34 Hooke-Jeeves pattern search: the exploratory probe and the pattern
  (acceleration) move over vector-valued state. An exploratory move adds a step
  vector to the base; when it improves, the pattern move accelerates in the same
  direction by extrapolating past the improved point:

      probe        = base + step
      pattern-move = improved + (improved - base)

  Both are finite-vector operations (add, subtract), reusing the n-dimensional
  vector state. This is a direct-search method: no gradient, just structured
  moves. The acceptance test that chooses whether to keep a probe stays an
  executable concern; what is proved here is the two move recurrences and worked
  two- and three-dimensional instances.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.hooke-jeeves`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.vector :as dep-finite-vector]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- vector-add [left right]
  (function/app (function/const* 'vector/add []) left right))
(defn- vector-subtract [left right]
  (function/app (function/const* 'vector/subtract []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- probe [base step]
  (function/app (function/const* 'hooke/probe []) base step))
(defn- pattern-move [base improved]
  (function/app (function/const* 'hooke/pattern-move []) base improved))

;; Definitions --------------------------------------------------------------

;; Exploratory move: step away from the base.
(def probe-spec
  {:name 'hooke/probe :kind :definition :universes []
   :type (function/arrow vector-type vector-type vector-type)
   :value (function/lam [['base vector-type] ['step vector-type]]
                        (vector-add 'base 'step))})

;; Pattern (acceleration) move: extrapolate past the improved point.
(def pattern-move-spec
  {:name 'hooke/pattern-move :kind :definition :universes []
   :type (function/arrow vector-type vector-type vector-type)
   :value (function/lam [['base vector-type] ['improved vector-type]]
                        (vector-add 'improved
                                    (vector-subtract 'improved 'base)))})

(def definition-specs [probe-spec pattern-move-spec])

;; Theorems -----------------------------------------------------------------

(def probe-unfold-spec
  {:name 'hooke/probe-unfold :universes []
   :type (function/forall
          [['base vector-type] ['step vector-type]]
          (equality vector-type (probe 'base 'step)
                    (vector-add 'base 'step)))
   :value (function/lam [['base vector-type] ['step vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type (probe 'base 'step)))})

(def pattern-move-unfold-spec
  {:name 'hooke/pattern-move-unfold :universes []
   :type (function/forall
          [['base vector-type] ['improved vector-type]]
          (equality vector-type (pattern-move 'base 'improved)
                    (vector-add 'improved
                                (vector-subtract 'improved 'base))))
   :value (function/lam [['base vector-type] ['improved vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type (pattern-move 'base 'improved)))})

;; Worked instances ---------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (function/app (function/const* 'data/nil [type-level]) signed)
          (reverse components)))

(def origin (make-vector (signed-numeral 0) (signed-numeral 0)))

;; probe [0,0] [1,2] = [1,2].
(def probe-example-spec
  {:name 'hooke/probe-example :universes []
   :type (equality vector-type
                   (probe origin (make-vector (signed-numeral 1)
                                              (signed-numeral 2)))
                   (make-vector (signed-numeral 1) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (probe origin (make-vector (signed-numeral 1)
                                                   (signed-numeral 2))))})

;; From base [0,0] and improved [1,2], accelerate to [1,2] + ([1,2]-[0,0]) = [2,4].
(def pattern-move-example-spec
  {:name 'hooke/pattern-move-example :universes []
   :type (equality vector-type
                   (pattern-move origin (make-vector (signed-numeral 1)
                                                     (signed-numeral 2)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (pattern-move origin (make-vector (signed-numeral 1)
                                                          (signed-numeral 2))))})

;; A three-dimensional pattern move: [0,0,0] base, [1,2,3] improved -> [2,4,6].
(def pattern-move-3d-example-spec
  {:name 'hooke/pattern-move-3d-example :universes []
   :type (equality vector-type
                   (pattern-move
                    (make-vector (signed-numeral 0) (signed-numeral 0)
                                 (signed-numeral 0))
                    (make-vector (signed-numeral 1) (signed-numeral 2)
                                 (signed-numeral 3)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)
                                (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (pattern-move
                         (make-vector (signed-numeral 0) (signed-numeral 0)
                                      (signed-numeral 0))
                         (make-vector (signed-numeral 1) (signed-numeral 2)
                                      (signed-numeral 3))))})

(def theorem-specs
  [probe-unfold-spec pattern-move-unfold-spec probe-example-spec
   pattern-move-example-spec pattern-move-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :hooke-jeeves (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.hooke-jeeves))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
