(ns rainbow.algorithms.proofs.admm
  "AHoF O51 ADMM (Alternating Direction Method of Multipliers): the scaled-form
  dual variable update over vector-valued state. After the x- and z-subproblems,
  the scaled dual variable accumulates the primal residual x - z:

      u' = u + (x - z)

  Every term is a finite-vector operation (subtract, add), reusing the shared
  n-dimensional vector state. The x-update argmin_x ( f(x) + (rho/2)||x - z + u||^2 )
  and the z-update are problem-specific minimizations supplied to the loop (not
  exact-rational in general and executable-only); what is proved here is the
  deterministic scaled dual recurrence and worked instances from a zero-
  initialized dual variable, where the residual passes through by reflexivity.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.admm`
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

(defn- dual-update [dual x z]
  (function/app (function/const* 'admm/dual-update []) dual x z))

;; Definitions --------------------------------------------------------------

;; u' = u + (x - z)
(def dual-update-spec
  {:name 'admm/dual-update :kind :definition :universes []
   :type (function/arrow vector-type vector-type vector-type vector-type)
   :value (function/lam [['dual vector-type] ['x vector-type] ['z vector-type]]
                        (vector-add 'dual
                                    (vector-subtract 'x 'z)))})

(def definition-specs [dual-update-spec])

;; Theorems -----------------------------------------------------------------

(def dual-update-unfold-spec
  {:name 'admm/dual-update-unfold :universes []
   :type (function/forall
          [['dual vector-type] ['x vector-type] ['z vector-type]]
          (equality vector-type
                    (dual-update 'dual 'x 'z)
                    (vector-add 'dual (vector-subtract 'x 'z))))
   :value (function/lam [['dual vector-type] ['x vector-type] ['z vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (dual-update 'dual 'x 'z)))})

;; Worked update from a zero-initialized dual variable ----------------------

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

(def zero-dual-2d (make-vector (signed-numeral 0) (signed-numeral 0)))
(def zero-dual-3d
  (make-vector (signed-numeral 0) (signed-numeral 0) (signed-numeral 0)))

;; When consensus is not yet reached the residual accumulates onto a zero dual:
;; [0,0] + ([3,2] - [0,0]) = [3,2].
(def residual-2d-example-spec
  {:name 'admm/residual-2d-example :universes []
   :type (equality vector-type
                   (dual-update zero-dual-2d
                                (make-vector (signed-numeral 3)
                                             (signed-numeral 2))
                                (make-vector (signed-numeral 0)
                                             (signed-numeral 0)))
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (dual-update zero-dual-2d
                                     (make-vector (signed-numeral 3)
                                                  (signed-numeral 2))
                                     (make-vector (signed-numeral 0)
                                                  (signed-numeral 0))))})

;; At consensus (x = z) the dual variable is unchanged: [0,0,0] + ([5,5,5] -
;; [5,5,5]) stays [0,0,0] -- but proving x - x = 0 needs the negation cancel
;; law, so the worked instance keeps z = 0 and lets the residual pass through.
(def residual-3d-example-spec
  {:name 'admm/residual-3d-example :universes []
   :type (equality vector-type
                   (dual-update zero-dual-3d
                                (make-vector (signed-numeral 2)
                                             (signed-numeral 4)
                                             (signed-numeral 6))
                                (make-vector (signed-numeral 0)
                                             (signed-numeral 0)
                                             (signed-numeral 0)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)
                                (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (dual-update zero-dual-3d
                                     (make-vector (signed-numeral 2)
                                                  (signed-numeral 4)
                                                  (signed-numeral 6))
                                     (make-vector (signed-numeral 0)
                                                  (signed-numeral 0)
                                                  (signed-numeral 0))))})

(def theorem-specs
  [dual-update-unfold-spec residual-2d-example-spec residual-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :admm (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.admm))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
