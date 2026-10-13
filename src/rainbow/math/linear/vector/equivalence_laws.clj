(ns rainbow.math.linear.vector.equivalence-laws
  "Structural laws for length-sensitive componentwise signed-vector equivalence.

  Reflexivity and symmetry are proved for arbitrary finite vectors by native
  List induction.  The map theorem is deliberately higher-order: any component
  function that respects signed equivalence respects vector equivalence when
  mapped over a list.  Vector negation congruence is then a specialization of
  that general theorem, while involutivity maps the corresponding scalar law
  over one list."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.order :as signed-order]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- nil-vector []
  (function/app (function/const* 'data/nil [type-level]) signed))

(defn- cons-vector [head tail]
  (function/app (function/const* 'data/cons [type-level])
                signed head tail))

(defn- list-map [mapping values]
  (function/app (function/const* 'list/map [type-level type-level])
                signed signed mapping values))

(defn- vector-negate [values]
  (function/app (function/const* 'vector/negate []) values))

(defn- signed-negate [value]
  (function/app (function/const* 'signed/negate []) value))

(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))

(defn- vector-equivalent [left right]
  (function/app (function/const* 'vector/equivalent []) left right))

(defn- conjunction [left right]
  (function/app (function/const* 'proposition/conjunction []) left right))

(defn- conjunction-left [left right evidence]
  (function/app (function/const* 'proposition/left [])
                left right evidence))

(defn- conjunction-right [left right evidence]
  (function/app (function/const* 'proposition/right [])
                left right evidence))

(defn- conjoin [left right left-evidence right-evidence]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-evidence right-evidence))

(def trivial (function/const* 'proposition/trivial []))

(defn- signed-equivalent-reflexive [value]
  (function/app (function/const* 'signed/equivalent-reflexive []) value))

(defn- signed-equivalent-symmetric [left right same]
  (function/app (function/const* 'signed/equivalent-symmetric [])
                left right same))

(defn- signed-negate-respects-equivalence [left right same]
  (function/app (function/const* 'signed/negate-respects-equivalence [])
                left right same))

(defn- signed-negate-involutive [value]
  (function/app (function/const* 'signed/negate-involutive []) value))

(defn- list-rec [motive base step values]
  (function/app
   (function/const* 'data/List.rec [type-level zero-level])
   signed motive base step values))

;; Every finite vector is componentwise equivalent to itself.  The empty case
;; is True; the cons case combines signed reflexivity with the induction
;; hypothesis for the tail.
(def equivalent-reflexive-spec
  {:name 'vector/equivalent-reflexive
   :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent 'values 'values))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent 'current 'current))
          step
          (function/lam
           [['head signed]
            ['tail vector-type]
            ['tail-reflexive (vector-equivalent 'tail 'tail)]]
           (conjoin
            (signed-equivalent 'head 'head)
            (vector-equivalent 'tail 'tail)
            (signed-equivalent-reflexive 'head)
            'tail-reflexive))]
      (list-rec motive trivial step 'values)))})

;; Length-sensitive vector equivalence is symmetric.  Both mismatch branches
;; reduce to False, so their evidence itself proves the reversed mismatch.
;; The cons/cons branch reverses the head proof and recursively reverses the
;; tail proof.
(def equivalent-symmetric-spec
  {:name 'vector/equivalent-symmetric
   :universes []
   :type
   (function/forall
    [['left vector-type]
     ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (vector-equivalent 'right 'left))
   :value
   (function/lam
    [['left vector-type]
     ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same
              (vector-equivalent 'current-left 'current-right)]]
            (vector-equivalent 'current-right 'current-left)))
          base
          (let [empty (nil-vector)
                inner-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-same
                    (vector-equivalent empty 'current-right)]]
                  (vector-equivalent 'current-right empty)))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              inner-motive
              (function/lam
               [['current-same (vector-equivalent empty empty)]]
               trivial)
              (function/lam
               [['right-head signed]
                ['right-tail vector-type]
                ['ignored (function/app inner-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (vector-equivalent
                   empty (cons-vector 'right-head 'right-tail))]]
                'current-same))
              'current-right)))
          step
          (function/lam
           [['left-head signed]
            ['left-tail vector-type]
            ['induction-hypothesis
             (function/app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 inner-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-same
                     (vector-equivalent current-left 'current-right)]]
                   (vector-equivalent 'current-right current-left)))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               inner-motive
               (function/lam
                [['current-same
                  (vector-equivalent current-left (nil-vector))]]
                'current-same)
               (function/lam
                [['right-head signed]
                 ['right-tail vector-type]
                 ['ignored (function/app inner-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (vector-equivalent
                    current-left (cons-vector 'right-head 'right-tail))]]
                 (let [head-proposition
                       (signed-equivalent 'left-head 'right-head)
                       tail-proposition
                       (vector-equivalent 'left-tail 'right-tail)
                       head-same
                       (conjunction-left head-proposition tail-proposition
                                         'current-same)
                       tail-same
                       (conjunction-right head-proposition tail-proposition
                                          'current-same)]
                   (conjoin
                    (signed-equivalent 'right-head 'left-head)
                    (vector-equivalent 'right-tail 'left-tail)
                    (signed-equivalent-symmetric
                     'left-head 'right-head head-same)
                    (function/app 'induction-hypothesis
                                  'right-tail tail-same)))))
               'current-right))))]
      (function/app (list-rec outer-motive base step 'left)
                    'right 'same)))})

;; A relation-preserving component map preserves vector equivalence.  This is
;; the reusable structural theorem: later component operations only need to
;; prove their scalar congruence once.
(def map-respects-equivalence-spec
  {:name 'vector/map-respects-equivalence
   :universes []
   :type
   (function/forall
    [['mapping (function/arrow signed signed)]
     ['respects
      (function/forall
       [['left-component signed]
        ['right-component signed]
        ['component-same
         (signed-equivalent 'left-component 'right-component)]]
       (signed-equivalent
        (function/app 'mapping 'left-component)
        (function/app 'mapping 'right-component)))]
     ['left vector-type]
     ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (vector-equivalent (list-map 'mapping 'left)
                       (list-map 'mapping 'right)))
   :value
   (function/lam
    [['mapping (function/arrow signed signed)]
     ['respects
      (function/forall
       [['left-component signed]
        ['right-component signed]
        ['component-same
         (signed-equivalent 'left-component 'right-component)]]
       (signed-equivalent
        (function/app 'mapping 'left-component)
        (function/app 'mapping 'right-component)))]
     ['left vector-type]
     ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same
              (vector-equivalent 'current-left 'current-right)]]
            (vector-equivalent
             (list-map 'mapping 'current-left)
             (list-map 'mapping 'current-right))))
          base
          (let [empty (nil-vector)
                inner-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-same
                    (vector-equivalent empty 'current-right)]]
                  (vector-equivalent
                   (list-map 'mapping empty)
                   (list-map 'mapping 'current-right))))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              inner-motive
              (function/lam
               [['current-same (vector-equivalent empty empty)]]
               trivial)
              (function/lam
               [['right-head signed]
                ['right-tail vector-type]
                ['ignored (function/app inner-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (vector-equivalent
                   empty (cons-vector 'right-head 'right-tail))]]
                'current-same))
              'current-right)))
          step
          (function/lam
           [['left-head signed]
            ['left-tail vector-type]
            ['induction-hypothesis
             (function/app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 inner-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-same
                     (vector-equivalent current-left 'current-right)]]
                   (vector-equivalent
                    (list-map 'mapping current-left)
                    (list-map 'mapping 'current-right))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               inner-motive
               (function/lam
                [['current-same
                  (vector-equivalent current-left (nil-vector))]]
                'current-same)
               (function/lam
                [['right-head signed]
                 ['right-tail vector-type]
                 ['ignored (function/app inner-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (vector-equivalent
                    current-left (cons-vector 'right-head 'right-tail))]]
                 (let [head-proposition
                       (signed-equivalent 'left-head 'right-head)
                       tail-proposition
                       (vector-equivalent 'left-tail 'right-tail)
                       head-same
                       (conjunction-left head-proposition tail-proposition
                                         'current-same)
                       tail-same
                       (conjunction-right head-proposition tail-proposition
                                          'current-same)
                       mapped-left-head
                       (function/app 'mapping 'left-head)
                       mapped-right-head
                       (function/app 'mapping 'right-head)]
                   (conjoin
                    (signed-equivalent mapped-left-head mapped-right-head)
                    (vector-equivalent
                     (list-map 'mapping 'left-tail)
                     (list-map 'mapping 'right-tail))
                    (function/app 'respects
                                  'left-head 'right-head head-same)
                    (function/app 'induction-hypothesis
                                  'right-tail tail-same)))))
               'current-right))))]
      (function/app (list-rec outer-motive base step 'left)
                    'right 'same)))})

;; Negation is the held-out specialization of the generic map theorem.
(def negate-respects-equivalence-spec
  {:name 'vector/negate-respects-equivalence
   :universes []
   :type
   (function/forall
    [['left vector-type]
     ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (vector-equivalent (vector-negate 'left)
                       (vector-negate 'right)))
   :value
   (function/lam
    [['left vector-type]
     ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [mapping (function/lam [['value signed]] (signed-negate 'value))
          respects
          (function/lam
           [['left-component signed]
            ['right-component signed]
            ['component-same
             (signed-equivalent 'left-component 'right-component)]]
           (signed-negate-respects-equivalence
            'left-component 'right-component 'component-same))]
      (function/app
       (function/const* 'vector/map-respects-equivalence [])
       mapping respects 'left 'right 'same)))})

(def negate-involutive-spec
  {:name 'vector/negate-involutive
   :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent
     (vector-negate (vector-negate 'values))
     'values))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-negate (vector-negate 'current))
            'current))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-involutive (function/app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (signed-negate (signed-negate 'head))
             'head)
            (vector-equivalent
             (vector-negate (vector-negate 'tail))
             'tail)
            (signed-negate-involutive 'head)
            'tail-involutive))]
      (list-rec motive trivial step 'values)))})

(def theorem-specs
  [equivalent-reflexive-spec
   equivalent-symmetric-spec
   map-respects-equivalence-spec
   negate-respects-equivalence-spec
   negate-involutive-spec])

(defn- extend-signed-negate-involutive-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment
                              'signed/negate-involutive)
    checked-environment
    (support/extend-with checked-environment :signed-order
                         [signed-order/negate-involutive-spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment extend-signed-negate-involutive-if-missing (support/extend-with :vector-equivalence-laws theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.equivalence-laws))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
