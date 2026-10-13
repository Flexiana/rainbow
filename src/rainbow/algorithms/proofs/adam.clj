(ns rainbow.algorithms.proofs.adam
  "AHoF O24 Adam: the first-moment (momentum) estimate and the preconditioned
  step direction. Adam keeps a decayed average of the gradient (the first
  moment) alongside RMSProp's decayed average of the squared gradient (the
  second moment), then steps in the direction of the first moment divided by the
  square root of the second moment:

      first-moment' = retain * first-moment + fresh * gradient
      direction     = first-moment / sqrt(second-moment)

  This composes exact-rational multiplication/addition (the moment update) with
  exact division (the preconditioning), reusing the perfect-square root witness
  from AdaGrad. Bias correction (dividing by 1 - beta^t) needs powers and
  subtraction and stays in the executable reference, as does the epsilon term;
  what is proved is the first-moment recurrence and a worked preconditioned
  direction.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.adam`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def half (function/const* 'nnrat/half []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- divide [left right]
  (function/app (function/const* 'nnrat/divide []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- first-moment [retain fresh prev grad]
  (function/app (function/const* 'adam/first-moment []) retain fresh prev grad))
(defn- direction [moment root]
  (function/app (function/const* 'adam/direction []) moment root))

(defn- cross-product-reflexivity [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

;; Definitions --------------------------------------------------------------

;; first-moment' = retain * prev + fresh * gradient
(def first-moment-spec
  {:name 'adam/first-moment :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['retain nnrat] ['fresh nnrat]
                         ['prev nnrat] ['grad nnrat]]
                        (add (multiply 'retain 'prev)
                             (multiply 'fresh 'grad)))})

;; direction = first-moment / sqrt(second-moment)  (root supplied as a witness)
(def direction-spec
  {:name 'adam/direction :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['moment nnrat] ['root nnrat]]
                        (divide 'moment 'root))})

(def definition-specs [first-moment-spec direction-spec])

;; Theorems -----------------------------------------------------------------

(def first-moment-unfold-spec
  {:name 'adam/first-moment-unfold :universes []
   :type (function/forall
          [['retain nnrat] ['fresh nnrat] ['prev nnrat] ['grad nnrat]]
          (equality nnrat (first-moment 'retain 'fresh 'prev 'grad)
                    (add (multiply 'retain 'prev) (multiply 'fresh 'grad))))
   :value (function/lam [['retain nnrat] ['fresh nnrat] ['prev nnrat]
                         ['grad nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (first-moment 'retain 'fresh 'prev 'grad)))})

;; First moment from a zero start: retain 1/2, fresh 1/2, prev 0, gradient 2
;; gives 1/2*0 + 1/2*2 = 1.
(def first-moment-example-spec
  {:name 'adam/first-moment-example :universes []
   :type (equivalent (first-moment half half (whole 0) (whole 2))
                     (function/const* 'nnrat/one []))
   :value (cross-product-reflexivity
           (first-moment half half (whole 0) (whole 2))
           (function/const* 'nnrat/one []))})

;; Preconditioned direction: first moment 1 over second-moment root 2 gives 1/2.
(def direction-example-spec
  {:name 'adam/direction-example :universes []
   :type (equivalent (direction (function/const* 'nnrat/one []) (whole 2)) half)
   :value (cross-product-reflexivity
           (direction (function/const* 'nnrat/one []) (whole 2)) half)})

(def theorem-specs
  [first-moment-unfold-spec first-moment-example-spec direction-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :adam
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
