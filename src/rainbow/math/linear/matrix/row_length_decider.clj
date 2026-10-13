(ns rainbow.math.linear.matrix.row-length-decider
  "Executable, sound dimension checking for finite signed matrices.

  `matrix/decide-row-length-compatible` computes one Boolean by comparing each
  row's exact natural length with the reference vector's length.  A successful
  result is converted, inside the kernel, into the abstract certificates used
  by matrix and LP theorems:

    decision = true -> row-length-compatible -> compatible -> rectangular.

  This is output verification for the dimension check.  It does not prove a
  host Clojure parser or arbitrary executable correct, and it does not inspect
  matrix entries.  Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.boolean-and :as boolean-and]
            [rainbow.math.linear.matrix.row-length-shape :as row-length]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.linear-order :as nat-order]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [target-level motive base step rows]
  (app (function/const* 'data/List.rec [type-level target-level])
       vector-type motive base step rows))
(defn- length-of [values]
  (app (function/const* 'vector/length []) values))
(defn- decide-nat-equality [left right]
  (app (function/const* 'nat/decide-equality []) left right))
(defn- bool-and [left right]
  (app (function/const* 'boolean/and []) left right))
(defn- decide-row-length-compatible [rows values]
  (app (function/const* 'matrix/decide-row-length-compatible []) rows values))
(defn- row-length-compatible [rows values]
  (app (function/const* 'matrix/row-length-compatible []) rows values))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- nat-equality [left right]
  (function/equality type-level nat left right))
(defn- bool-equality [left right]
  (function/equality type-level bool left right))
(defn- reflexive-nat [value]
  (app (function/const* 'equality/reflexive [type-level]) nat value))
(defn- reflexive-bool [value]
  (app (function/const* 'equality/reflexive [type-level]) bool value))
(defn- symmetric-bool [left right same]
  (app (function/const* 'equality/symmetric [type-level])
       bool left right same))
(defn- substitute
  [carrier left right same predicate at-left]
  (app (function/const* 'equality/substitution [type-level])
       carrier left right same predicate at-left))
(defn- successor-congruent [left right same]
  (app (function/const* 'equality/congruent-function
                        [type-level type-level])
       nat nat (function/const* 'data/succ []) left right same))
(defn- explode [goal impossible]
  (app (function/const* 'proposition/explode []) goal impossible))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def decide-row-length-compatible-spec
  {:name 'matrix/decide-row-length-compatible :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type vector-type bool)
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]]
    (app
     (matrix-rec
      type-level
      (function/lam
       [['ignored matrix-type]]
       (function/arrow vector-type bool))
      (function/lam [['ignored-values vector-type]] true-value)
      (function/lam
       [['row vector-type] ['tail matrix-type]
        ['tail-decision (function/arrow vector-type bool)]]
       (function/lam
        [['current-values vector-type]]
        (bool-and
         (decide-nat-equality (length-of 'row)
                              (length-of 'current-values))
         (app 'tail-decision 'current-values))))
      'rows)
     'values))})

(def nat-decide-equality-true-sound-spec
  {:name 'nat/decide-equality-true-sound :universes []
   :type
   (function/forall
    [['left nat] ['right nat]
     ['decided
      (bool-equality (decide-nat-equality 'left 'right) true-value)]]
    (nat-equality 'left 'right))
   :value
   (function/lam
    [['left nat] ['right nat]
     ['decided
      (bool-equality (decide-nat-equality 'left 'right) true-value)]]
    (let [outer-motive
          (function/lam
           [['current-left nat]]
           (function/forall
            [['current-right nat]
             ['current-decision
              (bool-equality
               (decide-nat-equality 'current-left 'current-right)
               true-value)]]
            (nat-equality 'current-left 'current-right)))
          outer-base
          (function/lam
           [['current-right nat]]
           (app
            (function/const* 'data/Nat.rec [zero-level])
            (function/lam
             [['right-value nat]]
             (function/arrow
              (bool-equality
               (decide-nat-equality (function/const* 'data/zero [])
                                    'right-value)
               true-value)
              (nat-equality (function/const* 'data/zero []) 'right-value)))
            (function/lam
             [['current-decision
               (bool-equality
                (decide-nat-equality
                 (function/const* 'data/zero [])
                 (function/const* 'data/zero []))
                true-value)]]
             (reflexive-nat (function/const* 'data/zero [])))
            (function/lam
             [['right-previous nat]
              ['ignored
               (function/arrow
                (bool-equality
                 (decide-nat-equality
                  (function/const* 'data/zero []) 'right-previous)
                 true-value)
                (nat-equality
                 (function/const* 'data/zero []) 'right-previous))]]
             (function/lam
              [['current-decision
                (bool-equality
                 (decide-nat-equality
                  (function/const* 'data/zero []) (succ 'right-previous))
                 true-value)]]
              (explode
               (nat-equality
                (function/const* 'data/zero []) (succ 'right-previous))
               (app (function/const* 'bool/false-not-true [])
                    'current-decision))))
            'current-right))
          outer-step
          (function/lam
           [['left-previous nat]
            ['previous-law (app outer-motive 'left-previous)]]
           (function/lam
            [['current-right nat]]
            (app
             (function/const* 'data/Nat.rec [zero-level])
             (function/lam
              [['right-value nat]]
              (function/arrow
               (bool-equality
                (decide-nat-equality (succ 'left-previous) 'right-value)
                true-value)
               (nat-equality (succ 'left-previous) 'right-value)))
             (function/lam
              [['current-decision
                (bool-equality
                 (decide-nat-equality
                  (succ 'left-previous) (function/const* 'data/zero []))
                 true-value)]]
              (explode
               (nat-equality
                (succ 'left-previous) (function/const* 'data/zero []))
               (app (function/const* 'bool/false-not-true [])
                    'current-decision)))
             (function/lam
              [['right-previous nat]
               ['ignored
                (function/arrow
                 (bool-equality
                  (decide-nat-equality (succ 'left-previous)
                                       'right-previous)
                  true-value)
                 (nat-equality (succ 'left-previous) 'right-previous))]]
              (function/lam
               [['current-decision
                 (bool-equality
                  (decide-nat-equality
                   (succ 'left-previous) (succ 'right-previous))
                  true-value)]]
               (successor-congruent
                'left-previous 'right-previous
                (app 'previous-law 'right-previous 'current-decision))))
             'current-right)))]
      (app
       (app (function/const* 'data/Nat.rec [zero-level])
            outer-motive outer-base outer-step 'left)
       'right 'decided)))})

(def decide-row-length-compatible-true-sound-spec
  {:name 'matrix/decide-row-length-compatible-true-sound :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['decided
      (bool-equality
       (decide-row-length-compatible 'rows 'values) true-value)]]
    (row-length-compatible 'rows 'values))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['decided
      (bool-equality
       (decide-row-length-compatible 'rows 'values) true-value)]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (function/forall
            [['current-values vector-type]
             ['current-decision
              (bool-equality
               (decide-row-length-compatible
                'current-rows 'current-values)
               true-value)]]
            (row-length-compatible 'current-rows 'current-values)))
          base
          (function/lam
           [['current-values vector-type]
            ['current-decision
             (bool-equality
              (decide-row-length-compatible
               (nil-matrix) 'current-values)
              true-value)]]
           trivial)
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-law (app motive 'tail)]]
           (function/lam
            [['current-values vector-type]
             ['current-decision
              (bool-equality
               (decide-row-length-compatible
                (cons-matrix 'row 'tail) 'current-values)
               true-value)]]
            (let [head-decision
                  (app (function/const* 'boolean/and-implies-left [])
                       (decide-nat-equality
                        (length-of 'row) (length-of 'current-values))
                       (decide-row-length-compatible
                        'tail 'current-values)
                       'current-decision)
                  tail-decision
                  (app (function/const* 'boolean/and-implies-right [])
                       (decide-nat-equality
                        (length-of 'row) (length-of 'current-values))
                       (decide-row-length-compatible
                        'tail 'current-values)
                       'current-decision)]
              (conjoin
               (nat-equality (length-of 'row)
                             (length-of 'current-values))
               (row-length-compatible 'tail 'current-values)
               (app (function/const* 'nat/decide-equality-true-sound [])
                    (length-of 'row) (length-of 'current-values)
                    head-decision)
               (app 'tail-law 'current-values tail-decision)))))]
      (app (matrix-rec zero-level motive base step 'rows)
           'values 'decided)))})

(def nat-decide-equality-reflexive-true-spec
  {:name 'nat/decide-equality-reflexive-true :universes []
   :type
   (function/forall
    [['value nat]]
    (bool-equality (decide-nat-equality 'value 'value) true-value))
   :value
   (function/lam
    [['value nat]]
    (app
     (function/const* 'data/Nat.rec [zero-level])
     (function/lam
      [['current nat]]
      (bool-equality
       (decide-nat-equality 'current 'current) true-value))
     (reflexive-bool true-value)
     (function/lam
      [['previous nat]
       ['previous-true
        (bool-equality
         (decide-nat-equality 'previous 'previous) true-value)]]
      'previous-true)
     'value))})

(def nat-equality-implies-decide-equality-true-spec
  {:name 'nat/equality-implies-decide-equality-true :universes []
   :type
   (function/forall
    [['left nat] ['right nat] ['same (nat-equality 'left 'right)]]
    (bool-equality (decide-nat-equality 'left 'right) true-value))
   :value
   (function/lam
    [['left nat] ['right nat] ['same (nat-equality 'left 'right)]]
    (substitute
     nat 'left 'right 'same
     (function/lam
      [['current-right nat]]
      (bool-equality
       (decide-nat-equality 'left 'current-right) true-value))
     (app (function/const* 'nat/decide-equality-reflexive-true [])
          'left)))})

(def boolean-and-true-introduction-spec
  {:name 'boolean/and-true-introduction :universes []
   :type
   (function/forall
    [['left bool] ['right bool]
     ['left-true (bool-equality 'left true-value)]
     ['right-true (bool-equality 'right true-value)]]
    (bool-equality (bool-and 'left 'right) true-value))
   :value
   (function/lam
    [['left bool] ['right bool]
     ['left-true (bool-equality 'left true-value)]
     ['right-true (bool-equality 'right true-value)]]
    (substitute
     bool true-value 'left
     (symmetric-bool 'left true-value 'left-true)
     (function/lam
      [['current-left bool]]
      (bool-equality (bool-and 'current-left 'right) true-value))
     'right-true))})

(def row-length-compatible-implies-decide-true-spec
  {:name 'matrix/row-length-compatible-implies-decide-true :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['certificate (row-length-compatible 'rows 'values)]]
    (bool-equality
     (decide-row-length-compatible 'rows 'values) true-value))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['certificate (row-length-compatible 'rows 'values)]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (function/forall
            [['current-values vector-type]
             ['current-certificate
              (row-length-compatible 'current-rows 'current-values)]]
            (bool-equality
             (decide-row-length-compatible
              'current-rows 'current-values)
             true-value)))
          base
          (function/lam
           [['current-values vector-type]
            ['current-certificate
             (row-length-compatible (nil-matrix) 'current-values)]]
           (reflexive-bool true-value))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-law (app motive 'tail)]]
           (function/lam
            [['current-values vector-type]
             ['current-certificate
              (row-length-compatible
               (cons-matrix 'row 'tail) 'current-values)]]
            (let [row-length-equality
                  (app (function/const* 'proposition/left [])
                       (nat-equality (length-of 'row)
                                     (length-of 'current-values))
                       (row-length-compatible 'tail 'current-values)
                       'current-certificate)
                  tail-certificate
                  (app (function/const* 'proposition/right [])
                       (nat-equality (length-of 'row)
                                     (length-of 'current-values))
                       (row-length-compatible 'tail 'current-values)
                       'current-certificate)
                  row-decision
                  (app
                   (function/const*
                    'nat/equality-implies-decide-equality-true [])
                   (length-of 'row) (length-of 'current-values)
                   row-length-equality)
                  tail-decision
                  (app 'tail-law 'current-values tail-certificate)]
              (app
               (function/const* 'boolean/and-true-introduction [])
               (decide-nat-equality
                (length-of 'row) (length-of 'current-values))
               (decide-row-length-compatible 'tail 'current-values)
               row-decision tail-decision))))]
      (app (matrix-rec zero-level motive base step 'rows)
           'values 'certificate)))})

(def decide-row-length-compatible-true-implies-compatible-spec
  {:name 'matrix/decide-row-length-compatible-true-implies-compatible
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['decided
      (bool-equality
       (decide-row-length-compatible 'rows 'values) true-value)]]
    (compatible 'rows 'values))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['decided
      (bool-equality
       (decide-row-length-compatible 'rows 'values) true-value)]]
    (app
     (function/const* 'matrix/row-length-compatible-implies-compatible [])
     'rows 'values
     (app
      (function/const* 'matrix/decide-row-length-compatible-true-sound [])
      'rows 'values 'decided)))})

(def decide-row-length-compatible-true-implies-rectangular-spec
  {:name 'matrix/decide-row-length-compatible-true-implies-rectangular
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['decided
      (bool-equality
       (decide-row-length-compatible 'rows 'values) true-value)]]
    (rectangular 'rows))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['decided
      (bool-equality
       (decide-row-length-compatible 'rows 'values) true-value)]]
    (app
     (function/const* 'matrix/row-length-compatible-implies-rectangular [])
     'rows 'values
     (app
      (function/const* 'matrix/decide-row-length-compatible-true-sound [])
      'rows 'values 'decided)))})

(def definition-specs [decide-row-length-compatible-spec])
(def theorem-specs
  [nat-decide-equality-true-sound-spec
   decide-row-length-compatible-true-sound-spec
   nat-decide-equality-reflexive-true-spec
   nat-equality-implies-decide-equality-true-spec
   boolean-and-true-introduction-spec
   row-length-compatible-implies-decide-true-spec
   decide-row-length-compatible-true-implies-compatible-spec
   decide-row-length-compatible-true-implies-rectangular-spec])

(defn- extend-specs-if-missing
  [checked-environment milestone specs]
  (reduce
   (fn [current spec]
     (if (environment/resolve-id current (:name spec))
       current
       (support/extend-with current milestone [spec])))
   checked-environment specs))

(defn extend-environment [checked-environment]
  (-> checked-environment
      row-length/extend-environment
      (extend-specs-if-missing
       :nat-linear-order [nat-order/nat-decide-equality-spec])
      (extend-specs-if-missing
       :boolean-and boolean-and/definition-specs)
      (extend-specs-if-missing
       :boolean-and boolean-and/theorem-specs)
      (support/extend-with :finite-matrix-row-length-decider
                           (into definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
