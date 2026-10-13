(ns rainbow.math.linear.matrix.mixed-sign-action
  "Mixed-sign laws for signed dot products and native matrix action.

  Addition preserves upper and lower zero bounds.  A nonpositive factor times
  a nonnegative factor is nonpositive, while two nonpositive factors have a
  nonnegative product.  Structural dot lifts cover the three remaining sign
  combinations, and rowwise lifting gives the corresponding matrix-vector
  action laws.  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.least-squares-equality :as equality]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & xs] (apply function/app f xs))
(defn- nv [] (app (function/const* 'data/nil [t]) signed))
(defn- cv [h q] (app (function/const* 'data/cons [t]) signed h q))
(defn- nm [] (app (function/const* 'data/nil [t]) vector-type))
(defn- cm [h q] (app (function/const* 'data/cons [t]) vector-type h q))
(defn- vr [m b s x]
  (app (function/const* 'data/List.rec [t z]) signed m b s x))
(defn- mr [m b s x]
  (app (function/const* 'data/List.rec [t z]) vector-type m b s x))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- vz [values] (app (function/const* 'vector/zero-like []) values))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- mz [rows] (app (function/const* 'matrix/zero-like []) rows))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- dot [a b] (app (function/const* 'vector/dot []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- conjp [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- pl [a b p]
  (app (function/const* 'proposition/left []) a b p))
(defn- prop-right [a b p]
  (app (function/const* 'proposition/right []) a b p))
(defn- scalar-sign [nonnegative? value]
  (if nonnegative? (sle signed-zero value) (sle value signed-zero)))
(defn- vector-sign [nonnegative? values]
  (if nonnegative?
    (vle (vz values) values)
    (vle values (vz values))))
(defn- matrix-sign [nonnegative? rows]
  (if nonnegative?
    (mle (mz rows) rows)
    (mle rows (mz rows))))

(def add-preserves-nonnegative-order-spec
  {:name 'signed/add-preserves-nonnegative-order :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-positive (sle signed-zero 'left)]
     ['right-positive (sle signed-zero 'right)]]
    (sle signed-zero (sadd 'left 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-positive (sle signed-zero 'left)]
     ['right-positive (sle signed-zero 'right)]]
    (let [sum (sadd 'left 'right)
          zero-sum (sadd signed-zero signed-zero)]
      (app
       (function/const* 'signed/at-most-respects-equivalence [])
       zero-sum signed-zero sum sum
       (app (function/const* 'signed/add-zero-right []) signed-zero)
       (app (function/const* 'signed/equivalent-reflexive []) sum)
       (app (function/const* 'signed/add-monotone [])
            signed-zero 'left signed-zero 'right
            'left-positive 'right-positive))))})

(def add-preserves-nonpositive-order-spec
  {:name 'signed/add-preserves-nonpositive-order :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-negative (sle 'left signed-zero)]
     ['right-negative (sle 'right signed-zero)]]
    (sle (sadd 'left 'right) signed-zero))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-negative (sle 'left signed-zero)]
     ['right-negative (sle 'right signed-zero)]]
    (let [sum (sadd 'left 'right)
          zero-sum (sadd signed-zero signed-zero)]
      (app
       (function/const* 'signed/at-most-respects-equivalence [])
       sum sum zero-sum signed-zero
       (app (function/const* 'signed/equivalent-reflexive []) sum)
       (app (function/const* 'signed/add-zero-right []) signed-zero)
       (app (function/const* 'signed/add-monotone [])
            'left signed-zero 'right signed-zero
            'left-negative 'right-negative))))})

(def multiply-nonpositive-nonnegative-order-spec
  {:name 'signed/multiply-nonpositive-nonnegative-order :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-negative (sle 'left signed-zero)]
     ['right-positive (sle signed-zero 'right)]]
    (sle (smul 'left 'right) signed-zero))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-negative (sle 'left signed-zero)]
     ['right-positive (sle signed-zero 'right)]]
    (let [start (smul 'right 'left)
          finish (smul 'left 'right)
          ordered
          (app
           (function/const*
            'optimization/signed-multiplier-penalty-nonpositive [])
           'right 'left 'right-positive 'left-negative)]
      (app
       (function/const* 'signed/at-most-respects-equivalence [])
       start finish signed-zero signed-zero
       (app (function/const* 'signed/multiply-commutative [])
            'right 'left)
       (app (function/const* 'signed/equivalent-reflexive [])
            signed-zero)
       ordered)))})

(def multiply-nonpositive-nonpositive-order-spec
  {:name 'signed/multiply-nonpositive-nonpositive-order :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-negative (sle 'left signed-zero)]
     ['right-negative (sle 'right signed-zero)]]
    (sle signed-zero (smul 'left 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-negative (sle 'left signed-zero)]
     ['right-negative (sle 'right signed-zero)]]
    (let [product (smul 'left 'right)]
      (app
       (function/const* 'signed/zero-at-most-of-nonnegative [])
       product
       (app (function/const* 'signed/multiply-nonpositive [])
            'left 'right
            (app (function/const* 'signed/nonpositive-of-at-most-zero [])
                 'left 'left-negative)
            (app (function/const* 'signed/nonpositive-of-at-most-zero [])
                 'right 'right-negative)))))})

(defn- dot-sign-lift
  [scalar-theorem left-nonnegative? right-nonnegative? result-nonnegative?]
  (function/lam
   [['left vector-type] ['right vector-type]
    ['left-sign (vector-sign left-nonnegative? 'left)]
    ['right-sign (vector-sign right-nonnegative? 'right)]]
   (let [om
         (function/lam
          [['l vector-type]]
          (function/forall
           [['r vector-type]
            ['ls (vector-sign left-nonnegative? 'l)]
            ['rs (vector-sign right-nonnegative? 'r)]]
           (scalar-sign result-nonnegative? (dot 'l 'r))))
         ob
         (function/lam
          [['r vector-type]
           ['ls (vector-sign left-nonnegative? (nv))]
           ['rs (vector-sign right-nonnegative? 'r)]]
          (app (function/const* 'signed/at-most-reflexive [])
               signed-zero))
         os
         (function/lam
          [['lh signed] ['lt vector-type] ['ih (app om 'lt)]]
          (let [l (cv 'lh 'lt)
                rm
                (function/lam
                 [['r vector-type]]
                 (function/forall
                  [['ls (vector-sign left-nonnegative? l)]
                   ['rs (vector-sign right-nonnegative? 'r)]]
                  (scalar-sign result-nonnegative? (dot l 'r))))]
            (function/lam
             [['r vector-type]]
             (vr
              rm
              (function/lam
               [['ls (vector-sign left-nonnegative? l)]
                ['rs (vector-sign right-nonnegative? (nv))]]
               (app (function/const* 'signed/at-most-reflexive [])
                    signed-zero))
              (function/lam
               [['rh signed] ['rt vector-type] ['ignored (app rm 'rt)]]
               (function/lam
                [['ls (vector-sign left-nonnegative? l)]
                 ['rs
                  (vector-sign right-nonnegative? (cv 'rh 'rt))]]
                (let [lhs (scalar-sign left-nonnegative? 'lh)
                      lts (vector-sign left-nonnegative? 'lt)
                      rhs (scalar-sign right-nonnegative? 'rh)
                      rts (vector-sign right-nonnegative? 'rt)
                      product (smul 'lh 'rh)
                      tail-dot (dot 'lt 'rt)
                      product-sign
                      (app (function/const* scalar-theorem [])
                           'lh 'rh
                           (pl lhs lts 'ls)
                           (pl rhs rts 'rs))
                      tail-sign
                      (app 'ih 'rt
                           (prop-right lhs lts 'ls)
                           (prop-right rhs rts 'rs))]
                  (app
                   (function/const*
                    (if result-nonnegative?
                      'signed/add-preserves-nonnegative-order
                      'signed/add-preserves-nonpositive-order)
                    [])
                   product tail-dot product-sign tail-sign))))
              'r))))]
     (app (vr om ob os 'left)
          'right 'left-sign 'right-sign))))

(def dot-nonpositive-left-spec
  {:name 'vector/dot-nonpositive-left :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['left-negative (vle 'left (vz 'left))]
     ['right-positive (vle (vz 'right) 'right)]]
    (sle (dot 'left 'right) signed-zero))
   :value
   (dot-sign-lift
    'signed/multiply-nonpositive-nonnegative-order
    false true false)})

(def dot-nonpositive-right-spec
  {:name 'vector/dot-nonpositive-right :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['left-positive (vle (vz 'left) 'left)]
     ['right-negative (vle 'right (vz 'right))]]
    (sle (dot 'left 'right) signed-zero))
   :value
   (dot-sign-lift
    'optimization/signed-multiplier-penalty-nonpositive
    true false false)})

(def dot-nonnegative-both-nonpositive-spec
  {:name 'vector/dot-nonnegative-both-nonpositive :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['left-negative (vle 'left (vz 'left))]
     ['right-negative (vle 'right (vz 'right))]]
    (sle signed-zero (dot 'left 'right)))
   :value
   (dot-sign-lift
    'signed/multiply-nonpositive-nonpositive-order
    false false true)})

(defn- action-sign-lift
  [dot-theorem rows-nonnegative? values-nonnegative? result-nonnegative?]
  (function/lam
   [['rows matrix-type] ['values vector-type]
    ['rows-sign (matrix-sign rows-nonnegative? 'rows)]
    ['values-sign (vector-sign values-nonnegative? 'values)]]
   (let [m
         (function/lam
          [['rs matrix-type]]
          (function/forall
           [['rs-sign (matrix-sign rows-nonnegative? 'rs)]]
           (vector-sign result-nonnegative? (action 'rs 'values))))
         b
         (function/lam
          [['rs-sign (matrix-sign rows-nonnegative? (nm))]]
          trivial)
         s
         (function/lam
          [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
          (function/lam
           [['rs-sign
             (matrix-sign rows-nonnegative? (cm 'row 'tail))]]
           (let [row-sign (vector-sign rows-nonnegative? 'row)
                 tail-sign (matrix-sign rows-nonnegative? 'tail)]
             (conjp
              (scalar-sign result-nonnegative? (dot 'row 'values))
              (vector-sign result-nonnegative? (action 'tail 'values))
              (app (function/const* dot-theorem [])
                   'row 'values
                   (pl row-sign tail-sign 'rs-sign)
                   'values-sign)
              (app 'ih (prop-right row-sign tail-sign 'rs-sign))))))]
     (app (mr m b s 'rows) 'rows-sign))))

(def action-nonpositive-rows-spec
  {:name 'matrix/vector-multiply-nonpositive-rows :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-negative (mle 'rows (mz 'rows))]
     ['values-positive (vle (vz 'values) 'values)]]
    (vle (action 'rows 'values) (vz (action 'rows 'values))))
   :value
   (action-sign-lift 'vector/dot-nonpositive-left false true false)})

(def action-nonpositive-values-spec
  {:name 'matrix/vector-multiply-nonpositive-values :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['values-negative (vle 'values (vz 'values))]]
    (vle (action 'rows 'values) (vz (action 'rows 'values))))
   :value
   (action-sign-lift 'vector/dot-nonpositive-right true false false)})

(def action-nonnegative-both-nonpositive-spec
  {:name 'matrix/vector-multiply-nonnegative-both-nonpositive :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-negative (mle 'rows (mz 'rows))]
     ['values-negative (vle 'values (vz 'values))]]
    (vle (vz (action 'rows 'values)) (action 'rows 'values)))
   :value
   (action-sign-lift
    'vector/dot-nonnegative-both-nonpositive false false true)})

(def definition-specs [])
(def theorem-specs
  [add-preserves-nonnegative-order-spec
   add-preserves-nonpositive-order-spec
   multiply-nonpositive-nonnegative-order-spec
   multiply-nonpositive-nonpositive-order-spec
   dot-nonpositive-left-spec
   dot-nonpositive-right-spec
   dot-nonnegative-both-nonpositive-spec
   action-nonpositive-rows-spec
   action-nonpositive-values-spec
   action-nonnegative-both-nonpositive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.least-squares-equality])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-mixed-sign-action theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.mixed-sign-action))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
