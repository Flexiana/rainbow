(ns rainbow.math.rational.signed.absolute
  "Native absolute value for signed rational proof data.

  `signed/absolute x` is the lattice expression `max x (-x)`.  It bounds both
  orientations of `x`, is nonnegative by decidable total-order case analysis,
  and is at most a threshold exactly when both linear deviation rows are.  This
  is the scalar prerequisite for signed-vector distances and quantitative
  affine contraction.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.deviation-rows :as deviation]))

(def z [:zero])
(def t [:succ z])
(def bool (function/const* 'data/Bool []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))

(defn- app [f & xs] (apply function/app f xs))
(defn- eq-bool [left right]
  (function/equality t bool left right))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- veq [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- absolute [value]
  (app (function/const* 'signed/absolute []) value))
(defn- both [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- left [left-prop right-prop evidence]
  (app (function/const* 'proposition/left [])
       left-prop right-prop evidence))
(defn- right [left-prop right-prop evidence]
  (app (function/const* 'proposition/right [])
       left-prop right-prop evidence))
(defn- transitive [left middle right left-middle middle-right]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right left-middle middle-right))

(def absolute-spec
  {:name 'signed/absolute :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed)
   :value
   (function/lam
    [['value signed]]
    (maximum 'value (negate 'value)))})

(def absolute-unfold-spec
  {:name 'signed/absolute-unfold :universes []
   :type
   (function/forall
    [['value signed]]
    (veq (absolute 'value)
         (maximum 'value (negate 'value))))
   :value
   (function/lam
    [['value signed]]
    (app (function/const* 'signed/equivalent-reflexive [])
         (maximum 'value (negate 'value))))})

(def at-most-absolute-spec
  {:name 'signed/at-most-absolute :universes []
   :type
   (function/forall
    [['value signed]]
    (sle 'value (absolute 'value)))
   :value
   (function/lam
    [['value signed]]
    (app (function/const* 'signed/max-upper-left [])
         'value (negate 'value)))})

(def negate-at-most-absolute-spec
  {:name 'signed/negate-at-most-absolute :universes []
   :type
   (function/forall
    [['value signed]]
    (sle (negate 'value) (absolute 'value)))
   :value
   (function/lam
    [['value signed]]
    (app (function/const* 'signed/max-upper-right [])
         'value (negate 'value)))})

(def absolute-nonnegative-spec
  {:name 'signed/absolute-nonnegative :universes []
   :type
   (function/forall
    [['value signed]]
    (sle signed-zero (absolute 'value)))
   :value
   (function/lam
    [['value signed]]
    (let [decision
          (app (function/const* 'signed/decide-at-most [])
               signed-zero 'value)
          target (sle signed-zero (absolute 'value))
          motive
          (function/lam
           [['choice bool]]
           (function/arrow (eq-bool decision 'choice) target))
          false-case
          (function/lam
           [['decided-false (eq-bool decision false-value)]]
           (let [value-zero
                 (app
                  (function/const*
                   'signed/decide-at-most-false-reverse [])
                  signed-zero 'value 'decided-false)
                 zero-negated
                 (app (function/const* 'signed/negate-reverses-order [])
                      'value signed-zero value-zero)]
             (transitive
              signed-zero (negate 'value) (absolute 'value)
              zero-negated
              (app (function/const* 'signed/max-upper-right [])
                   'value (negate 'value)))))
          true-case
          (function/lam
           [['decided-true (eq-bool decision true-value)]]
           (let [zero-value
                 (app
                  (function/const* 'signed/decide-at-most-true-sound [])
                  signed-zero 'value 'decided-true)]
             (transitive
              signed-zero 'value (absolute 'value)
              zero-value
              (app (function/const* 'signed/max-upper-left [])
                   'value (negate 'value)))))]
      (app
       (app (function/const* 'data/Bool.rec [z])
            motive false-case true-case decision)
       (app (function/const* 'equality/reflexive [t])
            bool decision))))})

(def absolute-bounded-iff-deviation-rows-spec
  {:name 'signed/absolute-bounded-iff-deviation-rows :universes []
   :type
   (function/forall
    [['value signed] ['threshold signed]]
    (proposition/equivalence
     (sle (absolute 'value) 'threshold)
     (both (sle 'value 'threshold)
           (sle (negate 'value) 'threshold))))
   :value
   (function/lam
    [['value signed] ['threshold signed]]
    (let [absolute-bound (sle (absolute 'value) 'threshold)
          value-bound (sle 'value 'threshold)
          negate-bound (sle (negate 'value) 'threshold)
          row-bounds (both value-bound negate-bound)]
      (app
       (function/const* 'proposition/equivalence-intro [])
       absolute-bound row-bounds
       (function/lam
        [['bounded absolute-bound]]
        (app (function/const* 'optimization/deviation-rows-complete [])
             'value 'threshold 'bounded))
       (function/lam
        [['rows-bounded row-bounds]]
        (app (function/const* 'optimization/deviation-rows-sound [])
             'value 'threshold
             (left value-bound negate-bound 'rows-bounded)
             (right value-bound negate-bound 'rows-bounded))))))})

(def definition-specs [absolute-spec])
(def theorem-specs
  [absolute-unfold-spec
   at-most-absolute-spec
   negate-at-most-absolute-spec
   absolute-nonnegative-spec
   absolute-bounded-iff-deviation-rows-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.deviation-rows])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :signed-absolute (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.absolute))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
