(ns rainbow.math.linear.vector.negate-additive
  "Native vector negation distributes over native vector addition.

    -(left + right)  ~  (-left) + (-right)

  Vector addition truncates to the shorter list, and both sides truncate at the
  same position.  The cons/cons case invokes signed/negate-additive and the tail
  induction hypothesis.  Native and axiom-free on D63."
  (:require [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.negate-additive :as signed-additive]
            [rainbow.math.linear.vector.equivalence :as vector-equivalence]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def trivial (function/const* 'proposition/trivial []))

(def negate-additive-spec
  {:name 'vector/negate-additive :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]]
    (vector-equivalent
     (vector-negate (vector-add 'left 'right))
     (vector-add
      (vector-negate 'left)
      (vector-negate 'right))))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]]
            (vector-equivalent
             (vector-negate (vector-add 'current-left 'current-right))
             (vector-add
              (vector-negate 'current-left)
              (vector-negate 'current-right)))))
          outer-base
          (function/lam
           [['current-right vector-type]]
           trivial)
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-additive (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (vector-equivalent
                   (vector-negate (vector-add current-left 'current-right))
                   (vector-add
                    (vector-negate current-left)
                    (vector-negate 'current-right))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               trivial
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (conjoin
                 (signed-equivalent
                  (signed-negate (signed-add 'left-head 'right-head))
                  (signed-add
                   (signed-negate 'left-head)
                   (signed-negate 'right-head)))
                 (vector-equivalent
                  (vector-negate (vector-add 'left-tail 'right-tail))
                  (vector-add
                   (vector-negate 'left-tail)
                   (vector-negate 'right-tail)))
                 (app (function/const* 'signed/negate-additive [])
                      'left-head 'right-head)
                 (app 'tail-additive 'right-tail)))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right)))})

(def definition-specs [])
(def theorem-specs [negate-additive-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      signed-additive/extend-environment
      finite-vector/extend-environment
      vector-equivalence/extend-environment
      (support/extend-with :vector-negate-additive theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
