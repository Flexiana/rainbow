(ns rainbow.algorithms.proofs.ahof.levenberg-marquardt
  "AHoF O31 worked Levenberg-Marquardt: the general descent skeleton with a damped
  Hessian-inverse step size, on the quadratic f(x) = x^2. The gradient is 2x, the
  Hessian is the constant 2, and the damping lambda is 2, so the step size is
  1 / (2 + 2) = 1/4. From x = 2 the step is 2 - (1/4)(2*2) = 1 -- a damped step,
  larger than Newton's leap to 0 (lambda = 0) but a real descent. The result is
  proved by signed cross-product equivalence.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.levenberg-marquardt`
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
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def two (make-rational (data-nat 2) (data-nat 0)))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))
(defn- signed-scale [rate value]
  (function/app (function/const* 'signed/scale []) rate value))
(defn- signed-subtract [left right]
  (function/app (function/const* 'signed/subtract []) left right))
(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))
(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))
(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))

(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(def hessian (function/const* 'ahof-o31/hessian []))
(def lambda (function/const* 'ahof-o31/lambda []))
(def direction (function/const* 'ahof-o31/direction []))
(def step-size (function/const* 'ahof-o31/step-size []))
(def update-rule (function/const* 'ahof-o31/update []))
(def initial (function/const* 'ahof-o31/initial []))

(defn- descent-iterate [steps start]
  (function/app (function/const* 'optimization/general-descent-iterate [])
                direction step-size update-rule steps start))

;; Definitions --------------------------------------------------------------

(def hessian-spec
  {:name 'ahof-o31/hessian :kind :definition :universes []
   :type (function/arrow signed nnrat)
   :value (function/lam [['ignored-point signed]] two)})

(def lambda-spec
  {:name 'ahof-o31/lambda :kind :definition :universes []
   :type nnrat :value two})

(def direction-spec
  {:name 'ahof-o31/direction :kind :definition :universes []
   :type (function/arrow signed signed)
   :value (function/lam [['point signed]] (signed-scale two 'point))})

(def step-size-spec
  {:name 'ahof-o31/step-size :kind :definition :universes []
   :type (function/arrow signed nnrat)
   :value (function/lam
           [['point signed]]
           (function/app
            (function/const* 'optimization/levenberg-marquardt-rate [])
            hessian lambda 'point))})

(def update-spec
  {:name 'ahof-o31/update :kind :definition :universes []
   :type (function/arrow signed nnrat signed signed)
   :value (function/lam [['point signed] ['rate nnrat] ['direction signed]]
                        (signed-subtract 'point (signed-scale 'rate
                                                              'direction)))})

(def initial-spec
  {:name 'ahof-o31/initial :kind :definition :universes []
   :type signed :value (from-nnrat two)})

(def trajectory-spec
  {:name 'ahof-o31/trajectory :kind :definition :universes []
   :type (function/arrow nat signed)
   :value (function/lam [['steps nat]] (descent-iterate 'steps initial))})

(def definition-specs
  [hessian-spec lambda-spec direction-spec step-size-spec update-spec
   initial-spec trajectory-spec])

;; Theorems -----------------------------------------------------------------

(def damped-step-spec
  (let [step-one (descent-iterate (data-nat 1) initial)
        at-one (from-nnrat nnrat-one)]
    {:name 'ahof-o31/damped-step-is-one :universes []
     :type (signed-equivalent step-one at-one)
     :value (signed-equivalent-cross step-one at-one)}))

(def recurrence-spec
  (let [step (function/lam
              [['step-index nat] ['previous signed]]
              (function/app
               (function/const* 'optimization/general-descent-step [])
               direction step-size update-rule 'previous))
        base-law (equality signed
                           (descent-iterate (function/const* 'data/zero [])
                                            initial)
                           initial)
        step-law (equality signed
                           (descent-iterate (data-nat 1) initial)
                           (function/app step (function/const* 'data/zero [])
                                         initial))]
    {:name 'ahof-o31/levenberg-marquardt-recurrence :universes []
     :type (proposition/conjunction base-law step-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law step-law
      (function/app
       (function/const* 'optimization/general-descent-iterate-zero [])
       direction step-size update-rule initial)
      (function/app (function/const* 'equality/reflexive [type-level])
                    signed (descent-iterate (data-nat 1) initial)))}))

(def levenberg-marquardt-spec
  (let [step-law (:type damped-step-spec)
        recurrence (:type recurrence-spec)]
    {:name 'ahof-o31/levenberg-marquardt :universes []
     :type (proposition/conjunction step-law recurrence)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      step-law recurrence
      (function/const* 'ahof-o31/damped-step-is-one [])
      (function/const* 'ahof-o31/levenberg-marquardt-recurrence []))}))

(def theorem-specs
  [damped-step-spec recurrence-spec levenberg-marquardt-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF Levenberg-Marquardt expression failed elaboration"
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
          {:origin :native :producer :ahof-o31-levenberg-marquardt}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF Levenberg-Marquardt declaration rejected"
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
