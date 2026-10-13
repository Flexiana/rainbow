(ns rainbow.algorithms.proofs.ahof.policy-gradient
  "AHoF D49 Gradient Ascent Update (policy gradient): the parameter update at the
  heart of policy-gradient reinforcement learning. Given a policy-gradient
  estimate, the parameters ascend along it by the learning rate:

      update theta rate gradient = theta + rate * gradient

  over the finite-vector parameter state. The gradient estimate (REINFORCE,
  reward-to-go, actor-critic, ...) and the learning-rate schedule are executable
  concerns; what is proved here is the deterministic ascent update and worked
  instances from a zero-initialized parameter, where a unit-rate step lands
  exactly on the gradient.

  Requires the shared finite-vector operations (vector/add, vector/scale) over
  signed rationals -- carried by the D63 checkpoint via the vector layer.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.policy-gradient`
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
(defn- vector-scale [rate value]
  (function/app (function/const* 'vector/scale []) rate value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- update-step [theta rate gradient]
  (function/app (function/const* 'policy-gradient/update []) theta rate gradient))

;; Definitions --------------------------------------------------------------

;; update theta rate gradient = theta + rate * gradient
(def update-spec
  {:name 'policy-gradient/update :kind :definition :universes []
   :type (function/arrow vector-type nnrat vector-type vector-type)
   :value (function/lam [['theta vector-type] ['rate nnrat]
                         ['gradient vector-type]]
                        (vector-add 'theta (vector-scale 'rate 'gradient)))})

(def definition-specs [update-spec])

;; Theorems -----------------------------------------------------------------

(def update-unfold-spec
  {:name 'policy-gradient/update-unfold :universes []
   :type (function/forall
          [['theta vector-type] ['rate nnrat] ['gradient vector-type]]
          (equality vector-type
                    (update-step 'theta 'rate 'gradient)
                    (vector-add 'theta (vector-scale 'rate 'gradient))))
   :value (function/lam [['theta vector-type] ['rate nnrat]
                         ['gradient vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (update-step 'theta 'rate 'gradient)))})

;; Worked update from zero-initialized parameters ---------------------------

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

(def one-rational (nnrat-numeral 1))
(def zero-theta-2d (make-vector (signed-numeral 0) (signed-numeral 0)))
(def zero-theta-3d
  (make-vector (signed-numeral 0) (signed-numeral 0) (signed-numeral 0)))

;; From zero parameters a unit-rate step lands on the gradient:
;; [0,0] + 1 * [3,2] = [3,2].
(def update-unit-2d-example-spec
  {:name 'policy-gradient/update-unit-2d-example :universes []
   :type (equality vector-type
                   (update-step zero-theta-2d one-rational
                                (make-vector (signed-numeral 3)
                                             (signed-numeral 2)))
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (update-step zero-theta-2d one-rational
                                     (make-vector (signed-numeral 3)
                                                  (signed-numeral 2))))})

;; The three-dimensional analogue: [0,0,0] + 1 * [2,4,6] = [2,4,6].
(def update-unit-3d-example-spec
  {:name 'policy-gradient/update-unit-3d-example :universes []
   :type (equality vector-type
                   (update-step zero-theta-3d one-rational
                                (make-vector (signed-numeral 2)
                                             (signed-numeral 4)
                                             (signed-numeral 6)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)
                                (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (update-step zero-theta-3d one-rational
                                     (make-vector (signed-numeral 2)
                                                  (signed-numeral 4)
                                                  (signed-numeral 6))))})

(def theorem-specs
  [update-unfold-spec update-unit-2d-example-spec update-unit-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with (dep-finite-vector/extend-environment checked-environment) :ahof-policy-gradient
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
