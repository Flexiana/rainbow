(ns rainbow.math.linear.vector.shape-add
  "Shape preservation for truncating vector addition and subtraction.

  Equal-shaped inputs make vector/add's truncating zip consume both lists at the
  same position.  A native two-list induction proves that the result has both
  input shapes.  Subtraction follows by composing negation shape preservation
  with the addition theorem.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.shape-map :as shape-map]))

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
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(def trivial (function/const* 'proposition/trivial []))

(defn- add-shapes [left right]
  (conjunction
   (same-shape (vector-add left right) left)
   (same-shape (vector-add left right) right)))

(def add-preserves-shape-spec
  {:name 'vector/add-preserves-shape :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (add-shapes 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same
              (same-shape 'current-left 'current-right)]]
            (add-shapes 'current-left 'current-right)))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-same (same-shape empty 'current-right)]]
                  (add-shapes empty 'current-right)))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-same (same-shape empty empty)]]
               (conjoin
                (same-shape (vector-add empty empty) empty)
                (same-shape (vector-add empty empty) empty)
                trivial trivial))
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (same-shape
                   empty (cons-vector 'right-head 'right-tail))]]
                (absurd
                 (add-shapes
                  empty (cons-vector 'right-head 'right-tail))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-preserves (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-same
                     (same-shape current-left 'current-right)]]
                   (add-shapes current-left 'current-right)))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-same
                  (same-shape current-left (nil-vector))]]
                (absurd
                 (add-shapes current-left (nil-vector))
                 'current-same))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (same-shape
                    current-left
                    (cons-vector 'right-head 'right-tail))]]
                 (let [head-zero
                       (signed-equivalent signed-zero signed-zero)
                       tail-shape (same-shape 'left-tail 'right-tail)
                       tail-same
                       (proposition-right
                        head-zero tail-shape 'current-same)
                       tail-both
                       (app 'tail-preserves 'right-tail tail-same)
                       tail-left
                       (proposition-left
                        (same-shape
                         (vector-add 'left-tail 'right-tail)
                         'left-tail)
                        (same-shape
                         (vector-add 'left-tail 'right-tail)
                         'right-tail)
                        tail-both)
                       tail-right
                       (proposition-right
                        (same-shape
                         (vector-add 'left-tail 'right-tail)
                         'left-tail)
                        (same-shape
                         (vector-add 'left-tail 'right-tail)
                         'right-tail)
                        tail-both)
                       result-left
                       (conjoin
                        head-zero
                        (same-shape
                         (vector-add 'left-tail 'right-tail)
                         'left-tail)
                        (app
                         (function/const* 'signed/equivalent-reflexive [])
                         signed-zero)
                        tail-left)
                       result-right
                       (conjoin
                        head-zero
                        (same-shape
                         (vector-add 'left-tail 'right-tail)
                         'right-tail)
                        (app
                         (function/const* 'signed/equivalent-reflexive [])
                         signed-zero)
                        tail-right)]
                   (conjoin
                    (same-shape
                     (vector-add
                      current-left
                      (cons-vector 'right-head 'right-tail))
                     current-left)
                    (same-shape
                     (vector-add
                      current-left
                      (cons-vector 'right-head 'right-tail))
                     (cons-vector 'right-head 'right-tail))
                    result-left result-right))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def add-preserves-left-shape-spec
  {:name 'vector/add-preserves-left-shape :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (same-shape (vector-add 'left 'right) 'left))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (proposition-left
     (same-shape (vector-add 'left 'right) 'left)
     (same-shape (vector-add 'left 'right) 'right)
     (app (function/const* 'vector/add-preserves-shape [])
          'left 'right 'same)))})

(def add-preserves-right-shape-spec
  {:name 'vector/add-preserves-right-shape :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (same-shape (vector-add 'left 'right) 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (proposition-right
     (same-shape (vector-add 'left 'right) 'left)
     (same-shape (vector-add 'left 'right) 'right)
     (app (function/const* 'vector/add-preserves-shape [])
          'left 'right 'same)))})

(def subtract-preserves-shape-spec
  {:name 'vector/subtract-preserves-shape :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (conjunction
     (same-shape (vector-subtract 'left 'right) 'left)
     (same-shape (vector-subtract 'left 'right) 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [negated (vector-negate 'right)
          negated-right
          (app (function/const* 'vector/negate-preserves-shape []) 'right)
          right-negated
          (app (function/const* 'vector/same-shape-symmetric [])
               negated 'right negated-right)
          left-negated
          (app (function/const* 'vector/same-shape-transitive [])
               'left 'right negated 'same right-negated)
          added-both
          (app (function/const* 'vector/add-preserves-shape [])
               'left negated left-negated)
          added-left
          (proposition-left
           (same-shape (vector-add 'left negated) 'left)
           (same-shape (vector-add 'left negated) negated)
           added-both)
          added-negated
          (proposition-right
           (same-shape (vector-add 'left negated) 'left)
           (same-shape (vector-add 'left negated) negated)
           added-both)
          added-right
          (app (function/const* 'vector/same-shape-transitive [])
               (vector-subtract 'left 'right) negated 'right
               added-negated negated-right)]
      (conjoin
       (same-shape (vector-subtract 'left 'right) 'left)
       (same-shape (vector-subtract 'left 'right) 'right)
       added-left added-right)))})

(def definition-specs [])
(def theorem-specs
  [add-preserves-shape-spec
   add-preserves-left-shape-spec
   add-preserves-right-shape-spec
   subtract-preserves-shape-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.shape-map])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :vector-shape-add theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.shape-add))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
