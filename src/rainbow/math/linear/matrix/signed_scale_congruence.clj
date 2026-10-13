(ns rainbow.math.linear.matrix.signed-scale-congruence
  "Quotient congruence for signed scalar, vector, and matrix scaling.

  Signed rationals are Grothendieck representatives, so algebraic module laws
  are only reusable when scaling transports representative equivalence.  This
  milestone proves factor congruence, value congruence, and their joint form for
  the scalar scale-difference operation, then lifts the same family through
  vectors and matrices.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.signed-scale-units :as units]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-ring :as signed-ring]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- vector-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- scalar-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- matrix-signed-scale [factor rows]
  (app (function/const* 'matrix/signed-scale []) factor rows))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- scale-difference [factor value]
  (signed-subtract
   (scalar-scale (positive factor) value)
   (scalar-scale (negative factor) value)))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- vector-transitive [left middle right first second]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right first second))
(defn- matrix-transitive [left middle right first second]
  (app (function/const* 'matrix/equivalent-transitive [])
       left middle right first second))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(def scale-difference-respects-factor-equivalence-spec
  {:name 'signed/scale-difference-respects-factor-equivalence :universes []
   :type
   (function/forall
    [['factor signed] ['factor* signed] ['value signed]
     ['same-factor (signed-equivalent 'factor 'factor*)]]
    (signed-equivalent
     (scale-difference 'factor 'value)
     (scale-difference 'factor* 'value)))
   :value
   (function/lam
    [['factor signed] ['factor* signed] ['value signed]
     ['same-factor (signed-equivalent 'factor 'factor*)]]
    (let [start (scale-difference 'factor 'value)
          product (signed-multiply 'factor 'value)
          product* (signed-multiply 'factor* 'value)
          finish (scale-difference 'factor* 'value)]
      (signed-transitive
       start product* finish
       (signed-transitive
        start product product*
        (app (function/const* 'signed/scale-difference-multiply [])
             'factor 'value)
        (app
         (function/const*
          'signed/multiply-right-respects-equivalence [])
         'factor 'factor* 'value 'same-factor))
       (signed-symmetric
        finish product*
        (app (function/const* 'signed/scale-difference-multiply [])
             'factor* 'value)))))})

(def scale-difference-respects-value-equivalence-spec
  {:name 'signed/scale-difference-respects-value-equivalence :universes []
   :type
   (function/forall
    [['factor signed] ['value signed] ['value* signed]
     ['same-value (signed-equivalent 'value 'value*)]]
    (signed-equivalent
     (scale-difference 'factor 'value)
     (scale-difference 'factor 'value*)))
   :value
   (function/lam
    [['factor signed] ['value signed] ['value* signed]
     ['same-value (signed-equivalent 'value 'value*)]]
    (let [start (scale-difference 'factor 'value)
          product (signed-multiply 'factor 'value)
          product* (signed-multiply 'factor 'value*)
          finish (scale-difference 'factor 'value*)]
      (signed-transitive
       start product* finish
       (signed-transitive
        start product product*
        (app (function/const* 'signed/scale-difference-multiply [])
             'factor 'value)
        (app
         (function/const*
          'signed/multiply-left-respects-equivalence [])
         'value 'value* 'factor 'same-value))
       (signed-symmetric
        finish product*
        (app (function/const* 'signed/scale-difference-multiply [])
             'factor 'value*)))))})

(def scale-difference-respects-equivalence-spec
  {:name 'signed/scale-difference-respects-equivalence :universes []
   :type
   (function/forall
    [['factor signed] ['factor* signed]
     ['value signed] ['value* signed]
     ['same-factor (signed-equivalent 'factor 'factor*)]
     ['same-value (signed-equivalent 'value 'value*)]]
    (signed-equivalent
     (scale-difference 'factor 'value)
     (scale-difference 'factor* 'value*)))
   :value
   (function/lam
    [['factor signed] ['factor* signed]
     ['value signed] ['value* signed]
     ['same-factor (signed-equivalent 'factor 'factor*)]
     ['same-value (signed-equivalent 'value 'value*)]]
    (let [start (scale-difference 'factor 'value)
          middle (scale-difference 'factor* 'value)
          finish (scale-difference 'factor* 'value*)]
      (signed-transitive
       start middle finish
       (app
        (function/const*
         'signed/scale-difference-respects-factor-equivalence [])
        'factor 'factor* 'value 'same-factor)
       (app
        (function/const*
         'signed/scale-difference-respects-value-equivalence [])
        'factor* 'value 'value* 'same-value))))})

(def vector-signed-scale-respects-factor-equivalence-spec
  {:name 'vector/signed-scale-respects-factor-equivalence :universes []
   :type
   (function/forall
    [['factor signed] ['factor* signed] ['values vector-type]
     ['same-factor (signed-equivalent 'factor 'factor*)]]
    (vector-equivalent
     (vector-signed-scale 'factor 'values)
     (vector-signed-scale 'factor* 'values)))
   :value
   (function/lam
    [['factor signed] ['factor* signed] ['values vector-type]
     ['same-factor (signed-equivalent 'factor 'factor*)]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-signed-scale 'factor 'current)
            (vector-signed-scale 'factor* 'current)))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-respects (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (scale-difference 'factor 'head)
             (scale-difference 'factor* 'head))
            (vector-equivalent
             (vector-signed-scale 'factor 'tail)
             (vector-signed-scale 'factor* 'tail))
            (app
             (function/const*
              'signed/scale-difference-respects-factor-equivalence [])
             'factor 'factor* 'head 'same-factor)
            'tail-respects))]
      (vector-rec motive trivial step 'values)))})

(def vector-signed-scale-respects-value-equivalence-spec
  {:name 'vector/signed-scale-respects-value-equivalence :universes []
   :type
   (function/forall
    [['factor signed] ['left vector-type] ['right vector-type]
     ['same-values (vector-equivalent 'left 'right)]]
    (vector-equivalent
     (vector-signed-scale 'factor 'left)
     (vector-signed-scale 'factor 'right)))
   :value
   (function/lam
    [['factor signed] ['left vector-type] ['right vector-type]
     ['same-values (vector-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same
              (vector-equivalent 'current-left 'current-right)]]
            (vector-equivalent
             (vector-signed-scale 'factor 'current-left)
             (vector-signed-scale 'factor 'current-right))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-same
                    (vector-equivalent empty 'current-right)]]
                  (vector-equivalent
                   (vector-signed-scale 'factor empty)
                   (vector-signed-scale 'factor 'current-right))))]
            (function/lam
             [['current-right vector-type]]
             (vector-rec
              right-motive
              (function/lam
               [['current-same (vector-equivalent empty empty)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (vector-equivalent
                   empty (cons-vector 'right-head 'right-tail))]]
                (absurd
                 (vector-equivalent
                  (vector-signed-scale 'factor empty)
                  (vector-signed-scale
                   'factor (cons-vector 'right-head 'right-tail)))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-respects (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-same
                     (vector-equivalent current-left 'current-right)]]
                   (vector-equivalent
                    (vector-signed-scale 'factor current-left)
                    (vector-signed-scale 'factor 'current-right))))]
             (function/lam
              [['current-right vector-type]]
              (vector-rec
               right-motive
               (function/lam
                [['current-same
                  (vector-equivalent current-left (nil-vector))]]
                (absurd
                 (vector-equivalent
                  (vector-signed-scale 'factor current-left)
                  (vector-signed-scale 'factor (nil-vector)))
                 'current-same))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (vector-equivalent
                    current-left
                    (cons-vector 'right-head 'right-tail))]]
                 (let [head-same
                       (proposition-left
                        (signed-equivalent 'left-head 'right-head)
                        (vector-equivalent 'left-tail 'right-tail)
                        'current-same)
                       tail-same
                       (proposition-right
                        (signed-equivalent 'left-head 'right-head)
                        (vector-equivalent 'left-tail 'right-tail)
                        'current-same)]
                   (conjoin
                    (signed-equivalent
                     (scale-difference 'factor 'left-head)
                     (scale-difference 'factor 'right-head))
                    (vector-equivalent
                     (vector-signed-scale 'factor 'left-tail)
                     (vector-signed-scale 'factor 'right-tail))
                    (app
                     (function/const*
                      'signed/scale-difference-respects-value-equivalence [])
                     'factor 'left-head 'right-head head-same)
                    (app 'tail-respects 'right-tail tail-same)))))
               'current-right))))]
      (app (vector-rec outer-motive outer-base outer-step 'left)
           'right 'same-values)))})

(def vector-signed-scale-respects-equivalence-spec
  {:name 'vector/signed-scale-respects-equivalence :universes []
   :type
   (function/forall
    [['factor signed] ['factor* signed]
     ['left vector-type] ['right vector-type]
     ['same-factor (signed-equivalent 'factor 'factor*)]
     ['same-values (vector-equivalent 'left 'right)]]
    (vector-equivalent
     (vector-signed-scale 'factor 'left)
     (vector-signed-scale 'factor* 'right)))
   :value
   (function/lam
    [['factor signed] ['factor* signed]
     ['left vector-type] ['right vector-type]
     ['same-factor (signed-equivalent 'factor 'factor*)]
     ['same-values (vector-equivalent 'left 'right)]]
    (let [start (vector-signed-scale 'factor 'left)
          middle (vector-signed-scale 'factor* 'left)
          finish (vector-signed-scale 'factor* 'right)]
      (vector-transitive
       start middle finish
       (app
        (function/const*
         'vector/signed-scale-respects-factor-equivalence [])
        'factor 'factor* 'left 'same-factor)
       (app
        (function/const*
         'vector/signed-scale-respects-value-equivalence [])
        'factor* 'left 'right 'same-values))))})

(def matrix-signed-scale-respects-factor-equivalence-spec
  {:name 'matrix/signed-scale-respects-factor-equivalence :universes []
   :type
   (function/forall
    [['factor signed] ['factor* signed] ['rows matrix-type]
     ['same-factor (signed-equivalent 'factor 'factor*)]]
    (matrix-equivalent
     (matrix-signed-scale 'factor 'rows)
     (matrix-signed-scale 'factor* 'rows)))
   :value
   (function/lam
    [['factor signed] ['factor* signed] ['rows matrix-type]
     ['same-factor (signed-equivalent 'factor 'factor*)]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-signed-scale 'factor 'current)
            (matrix-signed-scale 'factor* 'current)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-respects (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-signed-scale 'factor 'row)
             (vector-signed-scale 'factor* 'row))
            (matrix-equivalent
             (matrix-signed-scale 'factor 'tail)
             (matrix-signed-scale 'factor* 'tail))
            (app
             (function/const*
              'vector/signed-scale-respects-factor-equivalence [])
             'factor 'factor* 'row 'same-factor)
            'tail-respects))]
      (matrix-rec motive trivial step 'rows)))})

(def matrix-signed-scale-respects-value-equivalence-spec
  {:name 'matrix/signed-scale-respects-value-equivalence :universes []
   :type
   (function/forall
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['same-values (matrix-equivalent 'left 'right)]]
    (matrix-equivalent
     (matrix-signed-scale 'factor 'left)
     (matrix-signed-scale 'factor 'right)))
   :value
   (function/lam
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['same-values (matrix-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-same
              (matrix-equivalent 'current-left 'current-right)]]
            (matrix-equivalent
             (matrix-signed-scale 'factor 'current-left)
             (matrix-signed-scale 'factor 'current-right))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-equivalent empty 'current-right)]]
                  (matrix-equivalent
                   (matrix-signed-scale 'factor empty)
                   (matrix-signed-scale 'factor 'current-right))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-same (matrix-equivalent empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (matrix-equivalent
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (matrix-equivalent
                  (matrix-signed-scale 'factor empty)
                  (matrix-signed-scale
                   'factor (cons-matrix 'right-row 'right-tail)))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-respects (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-same
                     (matrix-equivalent current-left 'current-right)]]
                   (matrix-equivalent
                    (matrix-signed-scale 'factor current-left)
                    (matrix-signed-scale 'factor 'current-right))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-equivalent current-left (nil-matrix))]]
                (absurd
                 (matrix-equivalent
                  (matrix-signed-scale 'factor current-left)
                  (matrix-signed-scale 'factor (nil-matrix)))
                 'current-same))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [row-same
                       (proposition-left
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)
                       tail-same
                       (proposition-right
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)]
                   (conjoin
                    (vector-equivalent
                     (vector-signed-scale 'factor 'left-row)
                     (vector-signed-scale 'factor 'right-row))
                    (matrix-equivalent
                     (matrix-signed-scale 'factor 'left-tail)
                     (matrix-signed-scale 'factor 'right-tail))
                    (app
                     (function/const*
                      'vector/signed-scale-respects-value-equivalence [])
                     'factor 'left-row 'right-row row-same)
                    (app 'tail-respects 'right-tail tail-same)))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'same-values)))})

(def matrix-signed-scale-respects-equivalence-spec
  {:name 'matrix/signed-scale-respects-equivalence :universes []
   :type
   (function/forall
    [['factor signed] ['factor* signed]
     ['left matrix-type] ['right matrix-type]
     ['same-factor (signed-equivalent 'factor 'factor*)]
     ['same-values (matrix-equivalent 'left 'right)]]
    (matrix-equivalent
     (matrix-signed-scale 'factor 'left)
     (matrix-signed-scale 'factor* 'right)))
   :value
   (function/lam
    [['factor signed] ['factor* signed]
     ['left matrix-type] ['right matrix-type]
     ['same-factor (signed-equivalent 'factor 'factor*)]
     ['same-values (matrix-equivalent 'left 'right)]]
    (let [start (matrix-signed-scale 'factor 'left)
          middle (matrix-signed-scale 'factor* 'left)
          finish (matrix-signed-scale 'factor* 'right)]
      (matrix-transitive
       start middle finish
       (app
        (function/const*
         'matrix/signed-scale-respects-factor-equivalence [])
        'factor 'factor* 'left 'same-factor)
       (app
        (function/const*
         'matrix/signed-scale-respects-value-equivalence [])
        'factor* 'left 'right 'same-values))))})

(def definition-specs [])
(def theorem-specs
  [scale-difference-respects-factor-equivalence-spec
   scale-difference-respects-value-equivalence-spec
   scale-difference-respects-equivalence-spec
   vector-signed-scale-respects-factor-equivalence-spec
   vector-signed-scale-respects-value-equivalence-spec
   vector-signed-scale-respects-equivalence-spec
   matrix-signed-scale-respects-factor-equivalence-spec
   matrix-signed-scale-respects-value-equivalence-spec
   matrix-signed-scale-respects-equivalence-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.signed-scale-units])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/multiply-left-respects-equivalence :signed-multiply-ring signed-ring/multiply-left-respects-spec) (extend-spec-if-missing 'signed/multiply-right-respects-equivalence :signed-multiply-ring signed-ring/multiply-right-respects-spec) (support/extend-with :finite-matrix-signed-scale-congruence theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.signed-scale-congruence))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
