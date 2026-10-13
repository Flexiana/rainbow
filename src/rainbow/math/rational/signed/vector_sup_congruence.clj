(ns rainbow.math.rational.signed.vector-sup-congruence
  "Quotient-safe congruence of signed-list sup distance.

  Componentwise equivalent replacements on either argument preserve the
  truncating finite sup distance.  The left law is structural: equivalent
  lists have matching constructors, scalar distance transports equivalent
  heads, and the induction hypothesis transports tails.  Symmetry derives the
  right law, and transitivity composes the two-sided law.  No shape hypothesis
  is needed because each vector-equivalence proof already preserves the shape
  of the argument it replaces.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.vector-sup-distance :as sup]
            [rainbow.math.linear.vector.equivalence :as vector-equivalence]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & xs] (apply function/app f xs))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def sup-distance-left-respects-equivalence-spec
  {:name 'vector/sup-distance-left-respects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type]
     ['same (vector-equivalent 'left 'left-prime)]]
    (veq (sup-distance 'left 'right)
         (sup-distance 'left-prime 'right)))
   :value
   (function/lam
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type]
     ['same (vector-equivalent 'left 'left-prime)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-prime vector-type]
             ['current-same
              (vector-equivalent 'current-left 'current-prime)]
             ['current-right vector-type]]
            (veq (sup-distance 'current-left 'current-right)
                 (sup-distance 'current-prime 'current-right))))
          outer-base
          (let [empty (nil-vector)
                prime-motive
                (function/lam
                 [['current-prime vector-type]]
                 (function/forall
                  [['current-same
                    (vector-equivalent empty 'current-prime)]
                   ['current-right vector-type]]
                  (veq (sup-distance empty 'current-right)
                       (sup-distance 'current-prime 'current-right))))]
            (function/lam
             [['current-prime vector-type]]
             (list-rec
              prime-motive
              (function/lam
               [['current-same (vector-equivalent empty empty)]
                ['current-right vector-type]]
               (equivalent-reflexive signed-zero))
              (function/lam
               [['prime-head signed] ['prime-tail vector-type]
                ['ignored (app prime-motive 'prime-tail)]]
               (function/lam
                [['current-same
                  (vector-equivalent
                   empty (cons-vector 'prime-head 'prime-tail))]
                 ['current-right vector-type]]
                (absurd
                 (veq (sup-distance empty 'current-right)
                      (sup-distance
                       (cons-vector 'prime-head 'prime-tail)
                       'current-right))
                 'current-same)))
              'current-prime)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-congruent (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 prime-motive
                 (function/lam
                  [['current-prime vector-type]]
                  (function/forall
                   [['current-same
                     (vector-equivalent current-left 'current-prime)]
                    ['current-right vector-type]]
                   (veq (sup-distance current-left 'current-right)
                        (sup-distance 'current-prime 'current-right))))]
             (function/lam
              [['current-prime vector-type]]
              (list-rec
               prime-motive
               (function/lam
                [['current-same
                  (vector-equivalent current-left (nil-vector))]
                 ['current-right vector-type]]
                (absurd
                 (veq (sup-distance current-left 'current-right)
                      (sup-distance (nil-vector) 'current-right))
                 'current-same))
               (function/lam
                [['prime-head signed] ['prime-tail vector-type]
                 ['ignored-prime (app prime-motive 'prime-tail)]]
                (let [current-prime
                      (cons-vector 'prime-head 'prime-tail)]
                  (function/lam
                   [['current-same
                     (vector-equivalent current-left current-prime)]
                    ['current-right vector-type]]
                   (let [head-proposition
                         (veq 'left-head 'prime-head)
                         tail-proposition
                         (vector-equivalent 'left-tail 'prime-tail)
                         head-same
                         (proposition-left
                          head-proposition tail-proposition 'current-same)
                         tail-same
                         (proposition-right
                          head-proposition tail-proposition 'current-same)
                         right-motive
                         (function/lam
                          [['remaining vector-type]]
                          (veq
                           (sup-distance current-left 'remaining)
                           (sup-distance current-prime 'remaining)))]
                     (list-rec
                      right-motive
                      (equivalent-reflexive signed-zero)
                      (function/lam
                       [['right-head signed] ['right-tail vector-type]
                        ['ignored-right
                         (app right-motive 'right-tail)]]
                       (app
                        (function/const*
                         'signed/max-respects-equivalence [])
                        (scalar-distance 'left-head 'right-head)
                        (sup-distance 'left-tail 'right-tail)
                        (scalar-distance 'prime-head 'right-head)
                        (sup-distance 'prime-tail 'right-tail)
                        (app
                         (function/const*
                          'signed/distance-respects-equivalence [])
                         'left-head 'prime-head
                         'right-head 'right-head
                         head-same
                         (equivalent-reflexive 'right-head))
                        (app 'tail-congruent
                             'prime-tail tail-same 'right-tail)))
                      'current-right)))))
               'current-prime))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'left-prime 'same 'right)))})

(def sup-distance-right-respects-equivalence-spec
  {:name 'vector/sup-distance-right-respects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['same (vector-equivalent 'right 'right-prime)]]
    (veq (sup-distance 'left 'right)
         (sup-distance 'left 'right-prime)))
   :value
   (function/lam
    [['left vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['same (vector-equivalent 'right 'right-prime)]]
    (let [start (sup-distance 'left 'right)
          commuted-right (sup-distance 'right 'left)
          commuted-prime (sup-distance 'right-prime 'left)
          finish (sup-distance 'left 'right-prime)]
      (equivalent-transitive
       start commuted-prime finish
       (equivalent-transitive
        start commuted-right commuted-prime
        (app (function/const* 'vector/sup-distance-symmetric [])
             'left 'right)
        (app
         (function/const*
          'vector/sup-distance-left-respects-equivalence [])
         'right 'right-prime 'left 'same))
       (app (function/const* 'vector/sup-distance-symmetric [])
            'right-prime 'left))))})

(def sup-distance-respects-equivalence-spec
  {:name 'vector/sup-distance-respects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-same (vector-equivalent 'left 'left-prime)]
     ['right-same (vector-equivalent 'right 'right-prime)]]
    (veq (sup-distance 'left 'right)
         (sup-distance 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-same (vector-equivalent 'left 'left-prime)]
     ['right-same (vector-equivalent 'right 'right-prime)]]
    (equivalent-transitive
     (sup-distance 'left 'right)
     (sup-distance 'left-prime 'right)
     (sup-distance 'left-prime 'right-prime)
     (app
      (function/const*
       'vector/sup-distance-left-respects-equivalence [])
      'left 'left-prime 'right 'left-same)
     (app
      (function/const*
       'vector/sup-distance-right-respects-equivalence [])
      'left-prime 'right 'right-prime 'right-same)))})

(def definition-specs [])
(def theorem-specs
  [sup-distance-left-respects-equivalence-spec
   sup-distance-right-respects-equivalence-spec
   sup-distance-respects-equivalence-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.vector-sup-distance rainbow.math.linear.vector.equivalence])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :signed-vector-sup-congruence theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.vector-sup-congruence))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
