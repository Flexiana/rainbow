(ns rainbow.math.linear.vector.pointwise-order-laws
  "Partial-order laws and order-reversing negation for signed vectors.

  `vector/at-most` is transitive, negation reverses it componentwise, and mutual
  componentwise order implies `vector/equivalent`.  The latter is the correct
  antisymmetry conclusion for Grothendieck-pair signed rationals, whose
  mathematical equality is represented by signed/equivalent rather than raw
  pair equality.

  Dimension mismatch is handled constructively: vector/at-most reduces to
  proposition/falsity when exactly one list is empty, and those impossible
  witnesses eliminate the mismatch branches.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.deviation-rows :as deviation]
            [rainbow.math.rational.signed.equivalence-laws :as signed-equivalence]
            [rainbow.math.rational.signed.unit-laws :as signed-units]
            [rainbow.math.linear.vector.pointwise-order :as pointwise]))

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
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
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

(def negate-reverses-order-spec
  {:name 'vector/negate-reverses-order :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (vector-at-most
     (vector-negate 'right)
     (vector-negate 'left)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-ordered
              (vector-at-most 'current-left 'current-right)]]
            (vector-at-most
             (vector-negate 'current-right)
             (vector-negate 'current-left))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-ordered
                    (vector-at-most empty 'current-right)]]
                  (vector-at-most
                   (vector-negate 'current-right)
                   (vector-negate empty))))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-ordered (vector-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-ordered
                  (vector-at-most
                   empty (cons-vector 'right-head 'right-tail))]]
                'current-ordered))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-reverses (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-ordered
                     (vector-at-most current-left 'current-right)]]
                   (vector-at-most
                    (vector-negate 'current-right)
                    (vector-negate current-left))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-ordered
                  (vector-at-most current-left (nil-vector))]]
                'current-ordered)
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-ordered
                   (vector-at-most
                    current-left (cons-vector 'right-head 'right-tail))]]
                 (let [head-order (at-most 'left-head 'right-head)
                       tail-order (vector-at-most 'left-tail 'right-tail)]
                   (conjoin
                    (at-most (negate 'right-head) (negate 'left-head))
                    (vector-at-most
                     (vector-negate 'right-tail)
                     (vector-negate 'left-tail))
                    (app (function/const* 'signed/negate-reverses-order [])
                         'left-head 'right-head
                         (proposition-left
                          head-order tail-order 'current-ordered))
                    (app 'tail-reverses 'right-tail
                         (proposition-right
                          head-order tail-order 'current-ordered))))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right 'ordered)))})

(def at-most-transitive-spec
  {:name 'vector/at-most-transitive :universes []
   :type
   (function/forall
    [['left vector-type] ['middle vector-type] ['right vector-type]
     ['left-middle (vector-at-most 'left 'middle)]
     ['middle-right (vector-at-most 'middle 'right)]]
    (vector-at-most 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['middle vector-type] ['right vector-type]
     ['left-middle (vector-at-most 'left 'middle)]
     ['middle-right (vector-at-most 'middle 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-middle vector-type] ['current-right vector-type]
             ['current-left-middle
              (vector-at-most 'current-left 'current-middle)]
             ['current-middle-right
              (vector-at-most 'current-middle 'current-right)]]
            (vector-at-most 'current-left 'current-right)))
          outer-base
          (let [empty (nil-vector)
                middle-motive
                (function/lam
                 [['current-middle vector-type]]
                 (function/forall
                  [['current-right vector-type]
                   ['current-left-middle
                    (vector-at-most empty 'current-middle)]
                   ['current-middle-right
                    (vector-at-most 'current-middle 'current-right)]]
                  (vector-at-most empty 'current-right)))]
            (function/lam
             [['current-middle vector-type]]
             (list-rec
              middle-motive
              (function/lam
               [['current-right vector-type]]
               (let [right-motive
                     (function/lam
                      [['final-right vector-type]]
                      (function/forall
                       [['current-left-middle
                         (vector-at-most empty empty)]
                        ['current-middle-right
                         (vector-at-most empty 'final-right)]]
                       (vector-at-most empty 'final-right)))]
                 (list-rec
                  right-motive
                  (function/lam
                   [['current-left-middle (vector-at-most empty empty)]
                    ['current-middle-right (vector-at-most empty empty)]]
                   trivial)
                  (function/lam
                   [['right-head signed] ['right-tail vector-type]
                    ['ignored (app right-motive 'right-tail)]]
                   (function/lam
                    [['current-left-middle (vector-at-most empty empty)]
                     ['current-middle-right
                      (vector-at-most
                       empty (cons-vector 'right-head 'right-tail))]]
                    'current-middle-right))
                  'current-right)))
              (function/lam
               [['middle-head signed] ['middle-tail vector-type]
                ['ignored (app middle-motive 'middle-tail)]]
               (function/lam
                [['current-right vector-type]
                 ['current-left-middle
                  (vector-at-most
                   empty (cons-vector 'middle-head 'middle-tail))]
                 ['current-middle-right
                  (vector-at-most
                   (cons-vector 'middle-head 'middle-tail) 'current-right)]]
                (absurd (vector-at-most empty 'current-right)
                        'current-left-middle)))
              'current-middle)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-transitive (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 middle-motive
                 (function/lam
                  [['current-middle vector-type]]
                  (function/forall
                   [['current-right vector-type]
                    ['current-left-middle
                     (vector-at-most current-left 'current-middle)]
                    ['current-middle-right
                     (vector-at-most 'current-middle 'current-right)]]
                   (vector-at-most current-left 'current-right)))]
             (function/lam
              [['current-middle vector-type]]
              (list-rec
               middle-motive
               (function/lam
                [['current-right vector-type]
                 ['current-left-middle
                  (vector-at-most current-left (nil-vector))]
                 ['current-middle-right
                  (vector-at-most (nil-vector) 'current-right)]]
                (absurd (vector-at-most current-left 'current-right)
                        'current-left-middle))
               (function/lam
                [['middle-head signed] ['middle-tail vector-type]
                 ['ignored (app middle-motive 'middle-tail)]]
                (let [current-middle
                      (cons-vector 'middle-head 'middle-tail)
                      right-motive
                      (function/lam
                       [['current-right vector-type]]
                       (function/forall
                        [['current-left-middle
                          (vector-at-most current-left current-middle)]
                         ['current-middle-right
                          (vector-at-most current-middle 'current-right)]]
                        (vector-at-most current-left 'current-right)))]
                  (function/lam
                   [['current-right vector-type]]
                   (list-rec
                    right-motive
                    (function/lam
                     [['current-left-middle
                       (vector-at-most current-left current-middle)]
                      ['current-middle-right
                       (vector-at-most current-middle (nil-vector))]]
                     (absurd (vector-at-most current-left (nil-vector))
                             'current-middle-right))
                    (function/lam
                     [['right-head signed] ['right-tail vector-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (function/lam
                      [['current-left-middle
                        (vector-at-most current-left current-middle)]
                       ['current-middle-right
                        (vector-at-most
                         current-middle
                         (cons-vector 'right-head 'right-tail))]]
                      (let [left-head-order
                            (at-most 'left-head 'middle-head)
                            left-tail-order
                            (vector-at-most 'left-tail 'middle-tail)
                            right-head-order
                            (at-most 'middle-head 'right-head)
                            right-tail-order
                            (vector-at-most 'middle-tail 'right-tail)]
                        (conjoin
                         (at-most 'left-head 'right-head)
                         (vector-at-most 'left-tail 'right-tail)
                         (app (function/const* 'signed/at-most-transitive [])
                              'left-head 'middle-head 'right-head
                              (proposition-left
                               left-head-order left-tail-order
                               'current-left-middle)
                              (proposition-left
                               right-head-order right-tail-order
                               'current-middle-right))
                         (app 'tail-transitive 'middle-tail 'right-tail
                              (proposition-right
                               left-head-order left-tail-order
                               'current-left-middle)
                              (proposition-right
                               right-head-order right-tail-order
                               'current-middle-right))))))
                    'current-right))))
               'current-middle))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'middle 'right 'left-middle 'middle-right)))})

(def at-most-antisymmetric-spec
  {:name 'vector/at-most-antisymmetric :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['forward (vector-at-most 'left 'right)]
     ['backward (vector-at-most 'right 'left)]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['forward (vector-at-most 'left 'right)]
     ['backward (vector-at-most 'right 'left)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-forward
              (vector-at-most 'current-left 'current-right)]
             ['current-backward
              (vector-at-most 'current-right 'current-left)]]
            (vector-equivalent 'current-left 'current-right)))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-forward (vector-at-most empty 'current-right)]
                   ['current-backward (vector-at-most 'current-right empty)]]
                  (vector-equivalent empty 'current-right)))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-forward (vector-at-most empty empty)]
                ['current-backward (vector-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-forward
                  (vector-at-most
                   empty (cons-vector 'right-head 'right-tail))]
                 ['current-backward
                  (vector-at-most
                   (cons-vector 'right-head 'right-tail) empty)]]
                (absurd
                 (vector-equivalent
                  empty (cons-vector 'right-head 'right-tail))
                 'current-forward)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-antisymmetric (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-forward
                     (vector-at-most current-left 'current-right)]
                    ['current-backward
                     (vector-at-most 'current-right current-left)]]
                   (vector-equivalent current-left 'current-right)))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-forward
                  (vector-at-most current-left (nil-vector))]
                 ['current-backward
                  (vector-at-most (nil-vector) current-left)]]
                (absurd (vector-equivalent current-left (nil-vector))
                        'current-forward))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-forward
                   (vector-at-most
                    current-left (cons-vector 'right-head 'right-tail))]
                  ['current-backward
                   (vector-at-most
                    (cons-vector 'right-head 'right-tail) current-left)]]
                 (let [forward-head (at-most 'left-head 'right-head)
                       forward-tail (vector-at-most 'left-tail 'right-tail)
                       backward-head (at-most 'right-head 'left-head)
                       backward-tail (vector-at-most 'right-tail 'left-tail)]
                   (conjoin
                    (equivalent 'left-head 'right-head)
                    (vector-equivalent 'left-tail 'right-tail)
                    (app (function/const* 'signed/at-most-antisymmetric [])
                         'left-head 'right-head
                         (proposition-left
                          forward-head forward-tail 'current-forward)
                         (proposition-left
                          backward-head backward-tail 'current-backward))
                    (app 'tail-antisymmetric 'right-tail
                         (proposition-right
                          forward-head forward-tail 'current-forward)
                         (proposition-right
                          backward-head backward-tail 'current-backward))))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right 'forward 'backward)))})

(def equivalent-to-mutual-at-most-spec
  {:name 'vector/equivalent-to-mutual-at-most :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (conjunction (vector-at-most 'left 'right)
                 (vector-at-most 'right 'left)))
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
            (conjunction
             (vector-at-most 'current-left 'current-right)
             (vector-at-most 'current-right 'current-left))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-same
                    (vector-equivalent empty 'current-right)]]
                  (conjunction
                   (vector-at-most empty 'current-right)
                   (vector-at-most 'current-right empty))))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-same (vector-equivalent empty empty)]]
               (conjoin (vector-at-most empty empty)
                        (vector-at-most empty empty)
                        trivial trivial))
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (vector-equivalent
                   empty (cons-vector 'right-head 'right-tail))]]
                (absurd
                 (conjunction
                  (vector-at-most
                   empty (cons-vector 'right-head 'right-tail))
                  (vector-at-most
                   (cons-vector 'right-head 'right-tail) empty))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-mutual (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-same
                     (vector-equivalent current-left 'current-right)]]
                   (conjunction
                    (vector-at-most current-left 'current-right)
                    (vector-at-most 'current-right current-left))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-same
                  (vector-equivalent current-left (nil-vector))]]
                (absurd
                 (conjunction
                  (vector-at-most current-left (nil-vector))
                  (vector-at-most (nil-vector) current-left))
                 'current-same))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (vector-equivalent
                    current-left (cons-vector 'right-head 'right-tail))]]
                 (let [head-same (equivalent 'left-head 'right-head)
                       tail-same
                       (vector-equivalent 'left-tail 'right-tail)
                       head-proof
                       (proposition-left head-same tail-same 'current-same)
                       tail-proof
                       (proposition-right head-same tail-same 'current-same)
                       tail-bounds
                       (app 'tail-mutual 'right-tail tail-proof)
                       tail-forward
                       (proposition-left
                        (vector-at-most 'left-tail 'right-tail)
                        (vector-at-most 'right-tail 'left-tail)
                        tail-bounds)
                       tail-backward
                       (proposition-right
                        (vector-at-most 'left-tail 'right-tail)
                        (vector-at-most 'right-tail 'left-tail)
                        tail-bounds)
                       forward
                       (conjoin
                        (at-most 'left-head 'right-head)
                        (vector-at-most 'left-tail 'right-tail)
                        (app
                         (function/const* 'signed/equivalent-to-at-most [])
                         'left-head 'right-head head-proof)
                        tail-forward)
                       backward
                       (conjoin
                        (at-most 'right-head 'left-head)
                        (vector-at-most 'right-tail 'left-tail)
                        (app
                         (function/const* 'signed/equivalent-to-at-most [])
                         'right-head 'left-head
                         (app
                          (function/const* 'signed/equivalent-symmetric [])
                          'left-head 'right-head head-proof))
                        tail-backward)]
                   (conjoin
                    (vector-at-most current-left
                                    (cons-vector 'right-head 'right-tail))
                    (vector-at-most
                     (cons-vector 'right-head 'right-tail) current-left)
                    forward backward))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def equivalent-to-at-most-spec
  {:name 'vector/equivalent-to-at-most :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (vector-at-most 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (proposition-left
     (vector-at-most 'left 'right)
     (vector-at-most 'right 'left)
     (app (function/const* 'vector/equivalent-to-mutual-at-most [])
          'left 'right 'same)))})

(def definition-specs [])
(def theorem-specs
  [negate-reverses-order-spec
   at-most-transitive-spec at-most-antisymmetric-spec
   equivalent-to-mutual-at-most-spec equivalent-to-at-most-spec])

(defn- extend-signed-negate-order-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment
                              'signed/negate-reverses-order)
    checked-environment
    (support/extend-with checked-environment :signed-deviation-rows
                         [deviation/negate-reverses-order-spec])))

(defn- extend-signed-symmetry-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment
                              'signed/equivalent-symmetric)
    checked-environment
    (support/extend-with checked-environment :signed-equivalence-laws
                         [signed-equivalence/equivalent-symmetric-spec])))

(defn- extend-signed-equivalent-order-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment
                              'signed/equivalent-to-at-most)
    checked-environment
    (support/extend-with checked-environment :signed-unit-laws
                         [signed-units/equivalent-to-at-most-spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment extend-signed-negate-order-if-missing extend-signed-symmetry-if-missing extend-signed-equivalent-order-if-missing (support/extend-with :vector-pointwise-order-laws theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.pointwise-order-laws))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
