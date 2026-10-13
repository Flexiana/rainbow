(ns rainbow.math.linear.vector.norm-congruence
  "Quotient-safe congruence laws for native squared norms and norm witnesses.

    norm/norm-squared-respects-equivalence
    norm/is-norm-respects-vector-equivalence

  Vector equivalence is length-sensitive and componentwise.  A two-List
  induction transports each head square through signed multiplication
  congruence and each tail norm through the induction hypothesis.  Any exact
  norm witness then transports by signed equivalence transitivity."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-ring :as signed-ring]
            [rainbow.math.linear.vector.norm-expansion :as expansion]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
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
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- is-norm [values candidate]
  (app (function/const* 'norm/is-norm []) values candidate))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def norm-squared-respects-equivalence-spec
  {:name 'norm/norm-squared-respects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (signed-equivalent
     (norm-squared 'left) (norm-squared 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same
              (vector-equivalent 'current-left 'current-right)]]
            (signed-equivalent
             (norm-squared 'current-left)
             (norm-squared 'current-right))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-same
                    (vector-equivalent empty 'current-right)]]
                  (signed-equivalent
                   (norm-squared empty)
                   (norm-squared 'current-right))))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-same (vector-equivalent empty empty)]]
               (app (function/const* 'signed/equivalent-reflexive [])
                    signed-zero))
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (vector-equivalent
                   empty (cons-vector 'right-head 'right-tail))]]
                (absurd
                 (signed-equivalent
                  (norm-squared empty)
                  (norm-squared
                   (cons-vector 'right-head 'right-tail)))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-congruent (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-same
                     (vector-equivalent current-left 'current-right)]]
                   (signed-equivalent
                    (norm-squared current-left)
                    (norm-squared 'current-right))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-same
                  (vector-equivalent current-left (nil-vector))]]
                (absurd
                 (signed-equivalent
                  (norm-squared current-left)
                  (norm-squared (nil-vector)))
                 'current-same))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (vector-equivalent
                    current-left
                    (cons-vector 'right-head 'right-tail))]]
                 (let [head-proposition
                       (signed-equivalent 'left-head 'right-head)
                       tail-proposition
                       (vector-equivalent 'left-tail 'right-tail)
                       head-same
                       (proposition-left
                        head-proposition tail-proposition 'current-same)
                       tail-same
                       (proposition-right
                        head-proposition tail-proposition 'current-same)
                       left-square
                       (signed-multiply 'left-head 'left-head)
                       right-square
                       (signed-multiply 'right-head 'right-head)]
                   (app
                    (function/const* 'signed/add-respects-equivalence [])
                    left-square right-square
                    (norm-squared 'left-tail)
                    (norm-squared 'right-tail)
                    (app
                     (function/const*
                      'signed/multiply-respects-equivalence [])
                     'left-head 'right-head
                     'left-head 'right-head
                     head-same head-same)
                    (app 'tail-congruent 'right-tail tail-same)))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def is-norm-respects-vector-equivalence-spec
  {:name 'norm/is-norm-respects-vector-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['candidate signed]
     ['same (vector-equivalent 'left 'right)]
     ['witness (is-norm 'left 'candidate)]]
    (is-norm 'right 'candidate))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['candidate signed]
     ['same (vector-equivalent 'left 'right)]
     ['witness (is-norm 'left 'candidate)]]
    (let [square (signed-multiply 'candidate 'candidate)]
      (transitive
       square (norm-squared 'left) (norm-squared 'right)
       'witness
       (app
        (function/const* 'norm/norm-squared-respects-equivalence [])
        'left 'right 'same))))})

(def definition-specs [])
(def theorem-specs
  [norm-squared-respects-equivalence-spec
   is-norm-respects-vector-equivalence-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn- extend-specs-if-missing
  [checked-environment milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   checked-environment
   specs))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.norm-expansion])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-specs-if-missing :signed-multiply-ring signed-ring/theorem-specs) (support/extend-with :vector-norm-congruence theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.norm-congruence))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
