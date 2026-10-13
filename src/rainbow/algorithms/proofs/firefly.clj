(ns rainbow.algorithms.proofs.firefly
  "AHoF O46 Firefly Algorithm: the attraction move over vector-valued state. A
  dimmer firefly moves toward a brighter one by a fraction of their separation:

      x' = x + beta * (bright - x)

  Every term is a finite-vector operation (subtract, scale, add), reusing the
  n-dimensional vector state introduced for the population methods. The textbook
  attractiveness beta = beta0 * exp(-gamma r^2) is distance-dependent and not
  exact-rational; the worked instance supplies beta as a concrete nonnegative
  rational, so what is proved is the deterministic attraction recurrence and a
  worked two-dimensional move, not the distance-weighted stochastic dynamics
  (which stay an executable-only concern).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.firefly`
  prints this classification."
  (:require [rainbow.math.finite.vector :as dep-finite-vector]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- vector-add [left right]
  (function/app (function/const* 'vector/add []) left right))
(defn- vector-subtract [left right]
  (function/app (function/const* 'vector/subtract []) left right))
(defn- vector-scale [rate value]
  (function/app (function/const* 'vector/scale []) rate value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- attraction-step [position bright beta]
  (function/app (function/const* 'firefly/attraction-step [])
                position bright beta))

;; Definitions --------------------------------------------------------------

;; x' = x + beta * (bright - x)
(def attraction-step-spec
  {:name 'firefly/attraction-step :kind :definition :universes []
   :type (function/arrow vector-type vector-type nnrat vector-type)
   :value (function/lam [['position vector-type] ['bright vector-type]
                         ['beta nnrat]]
                        (vector-add 'position
                                    (vector-scale 'beta
                                                  (vector-subtract 'bright
                                                                   'position))))})

(def definition-specs [attraction-step-spec])

;; Theorems -----------------------------------------------------------------

(def attraction-unfold-spec
  {:name 'firefly/attraction-unfold :universes []
   :type (function/forall
          [['position vector-type] ['bright vector-type] ['beta nnrat]]
          (equality vector-type
                    (attraction-step 'position 'bright 'beta)
                    (vector-add 'position
                                (vector-scale 'beta
                                              (vector-subtract 'bright
                                                               'position)))))
   :value (function/lam [['position vector-type] ['bright vector-type]
                         ['beta nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (attraction-step 'position 'bright 'beta)))})

;; Worked two-dimensional attraction ----------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nnrat-numeral [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat []) (nnrat-numeral n)))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (function/app (function/const* 'data/nil [type-level]) signed)
          (reverse components)))

;; A firefly at the origin keeps the difference clean, so the move reduces by
;; reflexivity: [0,0] + 1 * ([3,2] - [0,0]) = [3,2].
(def one-rational (nnrat-numeral 1))
(def origin (make-vector (signed-numeral 0) (signed-numeral 0)))

(def full-attraction-example-spec
  {:name 'firefly/full-attraction-example :universes []
   :type (equality vector-type
                   (attraction-step origin
                                    (make-vector (signed-numeral 3)
                                                 (signed-numeral 2))
                                    one-rational)
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (attraction-step origin
                                         (make-vector (signed-numeral 3)
                                                      (signed-numeral 2))
                                         one-rational))})

;; Full attraction (beta = 1) lands exactly on the brighter firefly.
(def full-attraction-3d-example-spec
  {:name 'firefly/full-attraction-3d-example :universes []
   :type (equality vector-type
                   (attraction-step
                    (make-vector (signed-numeral 0) (signed-numeral 0)
                                 (signed-numeral 0))
                    (make-vector (signed-numeral 2) (signed-numeral 4)
                                 (signed-numeral 6))
                    one-rational)
                   (make-vector (signed-numeral 2) (signed-numeral 4)
                                (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (attraction-step
                         (make-vector (signed-numeral 0) (signed-numeral 0)
                                      (signed-numeral 0))
                         (make-vector (signed-numeral 2) (signed-numeral 4)
                                      (signed-numeral 6))
                         one-rational))})

(def theorem-specs
  [attraction-unfold-spec full-attraction-example-spec
   full-attraction-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with (dep-finite-vector/extend-environment checked-environment) :firefly
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
