(ns rainbow.math.linear.vector.uniform-clamp
  "Uniform box projection for finite signed-rational vectors.

    vector/uniform-clamp lower upper values
      = map (signed/clamp lower upper) values

  `vector/in-band` is proof data asserting that every component lies between
  the same lower and upper bounds.  Projection produces that evidence for every
  ordered interval, respects length-sensitive componentwise vector equivalence,
  and is idempotent up to vector equivalence.

  This lifts the scalar signed lattice into the n-dimensional representation
  already used by Rainbow's optimization algorithms.  It is the reusable core
  of uniform box constraints and projected first-order methods.  Native and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.clamp :as signed-clamp]
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
(defn- list-map [mapping values]
  (app (function/const* 'list/map [type-level type-level])
       signed signed mapping values))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- clamp [lower upper value]
  (app (function/const* 'signed/clamp []) lower upper value))
(defn- uniform-clamp [lower upper values]
  (app (function/const* 'vector/uniform-clamp []) lower upper values))
(defn- in-band [lower upper values]
  (app (function/const* 'vector/in-band []) lower upper values))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(def trivial (function/const* 'proposition/trivial []))

(def uniform-clamp-spec
  {:name 'vector/uniform-clamp :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed vector-type vector-type)
   :value
   (function/lam
    [['lower signed] ['upper signed] ['values vector-type]]
    (list-map (function/lam [['value signed]]
                            (clamp 'lower 'upper 'value))
              'values))})

(def in-band-spec
  {:name 'vector/in-band :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed vector-type 'Prop)
   :value
   (function/lam
    [['lower signed] ['upper signed] ['values vector-type]]
    (app (function/const* 'data/List.rec [type-level type-level])
         signed
         (function/lam [['ignored vector-type]] 'Prop)
         (function/const* 'proposition/truth [])
         (function/lam
          [['head signed] ['tail vector-type] ['tail-in-band 'Prop]]
          (conjunction
           (at-most 'lower 'head)
           (conjunction (at-most 'head 'upper) 'tail-in-band)))
         'values))})

(def in-band-empty-spec
  {:name 'vector/in-band-empty :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]]
    (in-band 'lower 'upper (nil-vector)))
   :value
   (function/lam [['lower signed] ['upper signed]] trivial)})

(def in-band-cons-spec
  {:name 'vector/in-band-cons :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['head signed] ['tail vector-type]
     ['above-lower (at-most 'lower 'head)]
     ['below-upper (at-most 'head 'upper)]
     ['tail-in-band (in-band 'lower 'upper 'tail)]]
    (in-band 'lower 'upper (cons-vector 'head 'tail)))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['head signed] ['tail vector-type]
     ['above-lower (at-most 'lower 'head)]
     ['below-upper (at-most 'head 'upper)]
     ['tail-in-band (in-band 'lower 'upper 'tail)]]
    (conjoin
     (at-most 'lower 'head)
     (conjunction (at-most 'head 'upper)
                  (in-band 'lower 'upper 'tail))
     'above-lower
     (conjoin (at-most 'head 'upper)
              (in-band 'lower 'upper 'tail)
              'below-upper 'tail-in-band)))})

(def uniform-clamp-in-band-spec
  {:name 'vector/uniform-clamp-in-band :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['ordered (at-most 'lower 'upper)]
     ['values vector-type]]
    (in-band 'lower 'upper
             (uniform-clamp 'lower 'upper 'values)))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['ordered (at-most 'lower 'upper)]
     ['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (in-band 'lower 'upper
                    (uniform-clamp 'lower 'upper 'current)))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-in-band
             (in-band 'lower 'upper
                      (uniform-clamp 'lower 'upper 'tail))]]
           (let [projected (clamp 'lower 'upper 'head)]
             (conjoin
              (at-most 'lower projected)
              (conjunction
               (at-most projected 'upper)
               (in-band 'lower 'upper
                        (uniform-clamp 'lower 'upper 'tail)))
              (app (function/const* 'signed/clamp-lower [])
                   'lower 'upper 'head 'ordered)
              (conjoin
               (at-most projected 'upper)
               (in-band 'lower 'upper
                        (uniform-clamp 'lower 'upper 'tail))
               (app (function/const* 'signed/clamp-upper [])
                    'lower 'upper 'head)
               'tail-in-band))))]
      (app (function/const* 'data/List.rec [type-level zero-level])
           signed motive trivial step 'values)))})

(def uniform-clamp-respects-equivalence-spec
  {:name 'vector/uniform-clamp-respects-equivalence :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (vector-equivalent
     (uniform-clamp 'lower 'upper 'left)
     (uniform-clamp 'lower 'upper 'right)))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [mapping
          (function/lam [['value signed]]
                        (clamp 'lower 'upper 'value))
          respects
          (function/lam
           [['left-component signed]
            ['right-component signed]
            ['component-same
             (signed-equivalent 'left-component 'right-component)]]
           (app (function/const* 'signed/clamp-respects-equivalence [])
                'lower 'lower 'upper 'upper
                'left-component 'right-component
                (app (function/const* 'signed/equivalent-reflexive []) 'lower)
                (app (function/const* 'signed/equivalent-reflexive []) 'upper)
                'component-same))
          outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same
              (vector-equivalent 'current-left 'current-right)]]
            (vector-equivalent
             (list-map mapping 'current-left)
             (list-map mapping 'current-right))))
          base
          (let [empty (nil-vector)
                inner-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-same
                    (vector-equivalent empty 'current-right)]]
                  (vector-equivalent
                   (list-map mapping empty)
                   (list-map mapping 'current-right))))]
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
                ['ignored (app inner-motive 'right-tail)]]
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
            ['induction-hypothesis (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 inner-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-same
                     (vector-equivalent current-left 'current-right)]]
                   (vector-equivalent
                    (list-map mapping current-left)
                    (list-map mapping 'current-right))))]
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
                 ['ignored (app inner-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (vector-equivalent
                    current-left (cons-vector 'right-head 'right-tail))]]
                 (let [head-proposition
                       (signed-equivalent 'left-head 'right-head)
                       tail-proposition
                       (vector-equivalent 'left-tail 'right-tail)
                       head-same
                       (proposition-left head-proposition tail-proposition
                                         'current-same)
                       tail-same
                       (proposition-right head-proposition tail-proposition
                                          'current-same)]
                   (conjoin
                    (signed-equivalent
                     (app mapping 'left-head)
                     (app mapping 'right-head))
                    (vector-equivalent
                     (list-map mapping 'left-tail)
                     (list-map mapping 'right-tail))
                    (app respects 'left-head 'right-head head-same)
                    (app 'induction-hypothesis 'right-tail tail-same)))))
               'current-right))))]
      (app (list-rec outer-motive base step 'left)
           'right 'same)))})

(def uniform-clamp-preserves-in-band-spec
  {:name 'vector/uniform-clamp-preserves-in-band :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed] ['values vector-type]
     ['bounded (in-band 'lower 'upper 'values)]]
    (vector-equivalent
     (uniform-clamp 'lower 'upper 'values) 'values))
   :value
   (function/lam
    [['lower signed] ['upper signed] ['values vector-type]
     ['bounded (in-band 'lower 'upper 'values)]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (function/forall
            [['bounded (in-band 'lower 'upper 'current)]]
            (vector-equivalent
             (uniform-clamp 'lower 'upper 'current) 'current)))
          base
          (function/lam
           [['bounded (in-band 'lower 'upper (nil-vector))]]
           trivial)
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-preserved
             (function/forall
              [['bounded (in-band 'lower 'upper 'tail)]]
              (vector-equivalent
               (uniform-clamp 'lower 'upper 'tail) 'tail))]
            ['bounded
             (in-band 'lower 'upper (cons-vector 'head 'tail))]]
           (let [lower-claim (at-most 'lower 'head)
                 upper-and-tail
                 (conjunction (at-most 'head 'upper)
                              (in-band 'lower 'upper 'tail))
                 lower-proof
                 (proposition-left lower-claim upper-and-tail 'bounded)
                 upper-tail-proof
                 (proposition-right lower-claim upper-and-tail 'bounded)
                 upper-proof
                 (proposition-left (at-most 'head 'upper)
                                   (in-band 'lower 'upper 'tail)
                                   upper-tail-proof)
                 tail-proof
                 (proposition-right (at-most 'head 'upper)
                                    (in-band 'lower 'upper 'tail)
                                    upper-tail-proof)]
             (conjoin
              (signed-equivalent (clamp 'lower 'upper 'head) 'head)
              (vector-equivalent
               (uniform-clamp 'lower 'upper 'tail) 'tail)
              (app (function/const* 'signed/clamp-in-band [])
                   'lower 'upper 'head lower-proof upper-proof)
              (app 'tail-preserved tail-proof))))]
      (app (app (function/const* 'data/List.rec [type-level zero-level])
                signed motive base step 'values)
           'bounded)))})

(def uniform-clamp-idempotent-spec
  {:name 'vector/uniform-clamp-idempotent :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['ordered (at-most 'lower 'upper)]
     ['values vector-type]]
    (vector-equivalent
     (uniform-clamp 'lower 'upper
                    (uniform-clamp 'lower 'upper 'values))
     (uniform-clamp 'lower 'upper 'values)))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['ordered (at-most 'lower 'upper)]
     ['values vector-type]]
    (app (function/const* 'vector/uniform-clamp-preserves-in-band [])
         'lower 'upper (uniform-clamp 'lower 'upper 'values)
         (app (function/const* 'vector/uniform-clamp-in-band [])
              'lower 'upper 'ordered 'values)))})

(def definition-specs [uniform-clamp-spec in-band-spec])
(def theorem-specs
  [in-band-empty-spec in-band-cons-spec
   uniform-clamp-in-band-spec
   uniform-clamp-respects-equivalence-spec
   uniform-clamp-preserves-in-band-spec
   uniform-clamp-idempotent-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.clamp rainbow.math.linear.vector.equivalence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :vector-uniform-clamp (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.uniform-clamp))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
