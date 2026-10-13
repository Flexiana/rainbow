(ns rainbow.algorithms.proofs.powell
  "AHoF O33 Powell's Method: the conjugate search-direction generated from a
  cycle of coordinate line minimizations. Where cyclic coordinate search (O32)
  descends along fixed axes, Powell adds a new direction equal to the net
  displacement of a whole cycle and rotates it into the direction set:

      net-direction = cycle-end - cycle-start

  This is the finite-vector difference of the cycle endpoints -- the distinctive
  Powell step (the direction-set update). The line minimizations themselves and
  the direction-set bookkeeping stay in the executable reference; what is proved
  here is the net-direction recurrence and worked instances.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.powell`
  prints this classification."
  (:require [rainbow.math.finite.vector :as dep-finite-vector]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- vector-subtract [left right]
  (function/app (function/const* 'vector/subtract []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- net-direction [start end]
  (function/app (function/const* 'powell/net-direction []) start end))

;; Definitions --------------------------------------------------------------

;; The new conjugate direction: the net displacement over a cycle.
(def net-direction-spec
  {:name 'powell/net-direction :kind :definition :universes []
   :type (function/arrow vector-type vector-type vector-type)
   :value (function/lam [['start vector-type] ['end vector-type]]
                        (vector-subtract 'end 'start))})

(def definition-specs [net-direction-spec])

;; Theorems -----------------------------------------------------------------

(def net-direction-unfold-spec
  {:name 'powell/net-direction-unfold :universes []
   :type (function/forall
          [['start vector-type] ['end vector-type]]
          (equality vector-type (net-direction 'start 'end)
                    (vector-subtract 'end 'start)))
   :value (function/lam [['start vector-type] ['end vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type (net-direction 'start 'end)))})

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

;; A cycle from the origin to [2,3] generates the conjugate direction [2,3].
(def net-direction-example-spec
  {:name 'powell/net-direction-example :universes []
   :type (equality vector-type
                   (net-direction origin (make-vector (signed-numeral 2)
                                                      (signed-numeral 3)))
                   (make-vector (signed-numeral 2) (signed-numeral 3)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (net-direction origin (make-vector (signed-numeral 2)
                                                           (signed-numeral 3))))})

;; A three-dimensional cycle: origin to [1,2,3] generates direction [1,2,3].
(def net-direction-3d-example-spec
  {:name 'powell/net-direction-3d-example :universes []
   :type (equality vector-type
                   (net-direction
                    (make-vector (signed-numeral 0) (signed-numeral 0)
                                 (signed-numeral 0))
                    (make-vector (signed-numeral 1) (signed-numeral 2)
                                 (signed-numeral 3)))
                   (make-vector (signed-numeral 1) (signed-numeral 2)
                                (signed-numeral 3)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (net-direction
                         (make-vector (signed-numeral 0) (signed-numeral 0)
                                      (signed-numeral 0))
                         (make-vector (signed-numeral 1) (signed-numeral 2)
                                      (signed-numeral 3))))})

(def theorem-specs
  [net-direction-unfold-spec net-direction-example-spec
   net-direction-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with (dep-finite-vector/extend-environment checked-environment) :powell
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
