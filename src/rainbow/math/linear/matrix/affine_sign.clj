(ns rainbow.math.linear.matrix.affine-sign
  "Cone preservation for vector addition and signed affine matrix action.

  Truncated pointwise vector addition preserves both the nonnegative and
  nonpositive cones.  Combining those generic lemmas with the four matrix
  action sign cases proves every affine sign combination in which the offset
  and linear image share a sign.  In particular, nonnegative Bellman data map
  nonnegative values back into the nonnegative cone.  Theorem-only and
  axiom-free on D63."
  (:require [rainbow.math.linear.matrix.affine-order :as affine-order]
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
(defn- vr [m b s x]
  (app (function/const* 'data/List.rec [t z]) signed m b s x))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- vadd [a b] (app (function/const* 'vector/add []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
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

(defn- vector-add-sign-spec [nonnegative?]
  (let [name (if nonnegative?
               'vector/add-nonnegative
               'vector/add-nonpositive)
        scalar-law (if nonnegative?
                     'signed/add-preserves-nonnegative-order
                     'signed/add-preserves-nonpositive-order)]
    {:name name :universes []
     :type
     (function/forall
      [['left vector-type] ['right vector-type]
       ['left-sign (vector-sign nonnegative? 'left)]
       ['right-sign (vector-sign nonnegative? 'right)]]
      (vector-sign nonnegative? (vadd 'left 'right)))
     :value
     (function/lam
      [['left vector-type] ['right vector-type]
       ['left-sign (vector-sign nonnegative? 'left)]
       ['right-sign (vector-sign nonnegative? 'right)]]
      (let [m
            (function/lam
             [['l vector-type]]
             (function/forall
              [['r vector-type]
               ['ls (vector-sign nonnegative? 'l)]
               ['rs (vector-sign nonnegative? 'r)]]
              (vector-sign nonnegative? (vadd 'l 'r))))
            b
            (function/lam
             [['r vector-type]
              ['ls (vector-sign nonnegative? (nv))]
              ['rs (vector-sign nonnegative? 'r)]]
             trivial)
            s
            (function/lam
             [['lh signed] ['lt vector-type] ['ih (app m 'lt)]]
             (let [l (cv 'lh 'lt)
                   rm
                   (function/lam
                    [['r vector-type]]
                    (function/forall
                     [['ls (vector-sign nonnegative? l)]
                      ['rs (vector-sign nonnegative? 'r)]]
                     (vector-sign nonnegative? (vadd l 'r))))]
               (function/lam
                [['r vector-type]]
                (vr
                 rm
                 (function/lam
                  [['ls (vector-sign nonnegative? l)]
                   ['rs (vector-sign nonnegative? (nv))]]
                  trivial)
                 (function/lam
                  [['rh signed] ['rt vector-type]
                   ['ignored (app rm 'rt)]]
                  (function/lam
                   [['ls (vector-sign nonnegative? l)]
                    ['rs (vector-sign nonnegative? (cv 'rh 'rt))]]
                   (let [lhs (scalar-sign nonnegative? 'lh)
                         lts (vector-sign nonnegative? 'lt)
                         rhs (scalar-sign nonnegative? 'rh)
                         rts (vector-sign nonnegative? 'rt)]
                     (conjp
                      (scalar-sign nonnegative? (sadd 'lh 'rh))
                      (vector-sign nonnegative? (vadd 'lt 'rt))
                      (app (function/const* scalar-law [])
                           'lh 'rh
                           (pl lhs lts 'ls)
                           (pl rhs rts 'rs))
                      (app 'ih 'rt
                           (prop-right lhs lts 'ls)
                           (prop-right rhs rts 'rs))))))
                 'r))))]
        (app (vr m b s 'left) 'right 'left-sign 'right-sign)))}))

(def vector-add-nonnegative-spec (vector-add-sign-spec true))
(def vector-add-nonpositive-spec (vector-add-sign-spec false))

(defn- affine-sign-spec
  [name result-nonnegative? offset-nonnegative?
   rows-nonnegative? values-nonnegative? action-law]
  {:name name :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['values vector-type]
     ['offset-sign (vector-sign offset-nonnegative? 'offset)]
     ['rows-sign (matrix-sign rows-nonnegative? 'rows)]
     ['values-sign (vector-sign values-nonnegative? 'values)]]
    (vector-sign result-nonnegative? (affine 'rows 'offset 'values)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['values vector-type]
     ['offset-sign (vector-sign offset-nonnegative? 'offset)]
     ['rows-sign (matrix-sign rows-nonnegative? 'rows)]
     ['values-sign (vector-sign values-nonnegative? 'values)]]
    (app (function/const*
          (if result-nonnegative?
            'vector/add-nonnegative
            'vector/add-nonpositive) [])
         'offset (action 'rows 'values) 'offset-sign
         (app (function/const* action-law [])
              'rows 'values 'rows-sign 'values-sign)))})

(def affine-action-nonnegative-spec
  (affine-sign-spec
   'matrix/affine-action-nonnegative true true true true
   'matrix/vector-multiply-nonnegative))

(def affine-action-nonpositive-rows-spec
  (affine-sign-spec
   'matrix/affine-action-nonpositive-rows false false false true
   'matrix/vector-multiply-nonpositive-rows))

(def affine-action-nonpositive-values-spec
  (affine-sign-spec
   'matrix/affine-action-nonpositive-values false false true false
   'matrix/vector-multiply-nonpositive-values))

(def affine-action-nonnegative-both-nonpositive-spec
  (affine-sign-spec
   'matrix/affine-action-nonnegative-both-nonpositive
   true true false false
   'matrix/vector-multiply-nonnegative-both-nonpositive))

(def definition-specs [])
(def theorem-specs
  [vector-add-nonnegative-spec
   vector-add-nonpositive-spec
   affine-action-nonnegative-spec
   affine-action-nonpositive-rows-spec
   affine-action-nonpositive-values-spec
   affine-action-nonnegative-both-nonpositive-spec])

(defn extend-environment [env]
  (-> env
      affine-order/extend-environment
      (support/extend-with :finite-matrix-affine-sign theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
