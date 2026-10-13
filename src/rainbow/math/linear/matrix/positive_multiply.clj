(ns rainbow.math.linear.matrix.positive-multiply
  "Nonnegativity and monotonicity of native finite matrix multiplication.

  Transpose turns a nonnegative right matrix into nonnegative columns, so the
  positive matrix-action laws lift rowwise to products.  Multiplication is
  monotone in its left factor when the fixed right factor is nonnegative, in
  its right factor when the fixed left factor is nonnegative, and jointly
  monotone under the exact source/destination positivity premises needed by
  the two-step order path.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.transpose-order :as transpose-order]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & xs] (apply function/app f xs))
(defn- nm [] (app (function/const* 'data/nil [t]) vector-type))
(defn- cm [h q] (app (function/const* 'data/cons [t]) vector-type h q))
(defn- mr [m b s x]
  (app (function/const* 'data/List.rec [t z]) vector-type m b s x))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- conjp [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- pl [a b p]
  (app (function/const* 'proposition/left []) a b p))
(defn- prop-right [a b p]
  (app (function/const* 'proposition/right []) a b p))
(defn- absurd [goal bad] (app bad goal))

(def multiply-nonnegative-spec
  {:name 'matrix/multiply-nonnegative :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['left-positive (mle (mz 'left) 'left)]
     ['right-positive (mle (mz 'right) 'right)]]
    (mle (mz (multiply 'left 'right))
         (multiply 'left 'right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['left-positive (mle (mz 'left) 'left)]
     ['right-positive (mle (mz 'right) 'right)]]
    (let [columns (transpose 'right)
          columns-positive
          (app (function/const* 'matrix/transpose-nonnegative [])
               'right 'right-positive)
          m
          (function/lam
           [['rows matrix-type]]
           (function/forall
            [['positive (mle (mz 'rows) 'rows)]]
            (mle (mz (multiply 'rows 'right))
                 (multiply 'rows 'right))))
          b
          (function/lam
           [['positive (mle (mz (nm)) (nm))]]
           trivial)
          s
          (function/lam
           [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
           (function/lam
            [['positive
              (mle (mz (cm 'row 'tail)) (cm 'row 'tail))]]
            (let [row-positive (vle (vz 'row) 'row)
                  tail-positive (mle (mz 'tail) 'tail)]
              (conjp
               (vle (vz (action columns 'row))
                    (action columns 'row))
               (mle (mz (multiply 'tail 'right))
                    (multiply 'tail 'right))
               (app (function/const*
                     'matrix/vector-multiply-nonnegative [])
                    columns 'row columns-positive
                    (pl row-positive tail-positive 'positive))
               (app 'ih
                    (prop-right row-positive tail-positive
                                'positive))))))]
      (app (mr m b s 'left) 'left-positive)))})

(def multiply-monotone-left-spec
  {:name 'matrix/multiply-monotone-left :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['factor matrix-type]
     ['factor-positive (mle (mz 'factor) 'factor)]
     ['ordered (mle 'left 'right)]]
    (mle (multiply 'left 'factor)
         (multiply 'right 'factor)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['factor matrix-type]
     ['factor-positive (mle (mz 'factor) 'factor)]
     ['ordered (mle 'left 'right)]]
    (let [columns (transpose 'factor)
          columns-positive
          (app (function/const* 'matrix/transpose-nonnegative [])
               'factor 'factor-positive)
          om
          (function/lam
           [['l matrix-type]]
           (function/forall
            [['r matrix-type] ['ord (mle 'l 'r)]]
            (mle (multiply 'l 'factor)
                 (multiply 'r 'factor))))
          ob
          (let [e (nm)
                rm
                (function/lam
                 [['r matrix-type]]
                 (function/forall
                  [['ord (mle e 'r)]]
                  (mle (multiply e 'factor)
                       (multiply 'r 'factor))))]
            (function/lam
             [['r matrix-type]]
             (mr
              rm
              (function/lam [['ord (mle e e)]] trivial)
              (function/lam
               [['row vector-type] ['tail matrix-type]
                ['ignored (app rm 'tail)]]
               (function/lam
                [['ord (mle e (cm 'row 'tail))]]
                (absurd
                 (mle (multiply e 'factor)
                      (multiply (cm 'row 'tail) 'factor))
                 'ord)))
              'r)))
          os
          (function/lam
           [['lrow vector-type] ['ltail matrix-type]
            ['ih (app om 'ltail)]]
           (let [l (cm 'lrow 'ltail)
                 rm
                 (function/lam
                  [['r matrix-type]]
                  (function/forall
                   [['ord (mle l 'r)]]
                   (mle (multiply l 'factor)
                        (multiply 'r 'factor))))]
             (function/lam
              [['r matrix-type]]
              (mr
               rm
               (function/lam
                [['ord (mle l (nm))]]
                (absurd
                 (mle (multiply l 'factor)
                      (multiply (nm) 'factor))
                 'ord))
               (function/lam
                [['rrow vector-type] ['rtail matrix-type]
                 ['ignored (app rm 'rtail)]]
                (function/lam
                 [['ord (mle l (cm 'rrow 'rtail))]]
                 (let [row-order (vle 'lrow 'rrow)
                       tail-order (mle 'ltail 'rtail)]
                   (conjp
                    (vle (action columns 'lrow)
                         (action columns 'rrow))
                    (mle (multiply 'ltail 'factor)
                         (multiply 'rtail 'factor))
                    (app
                     (function/const*
                      'matrix/vector-multiply-monotone-values [])
                     columns 'lrow 'rrow columns-positive
                     (pl row-order tail-order 'ord))
                    (app 'ih 'rtail
                         (prop-right row-order tail-order 'ord))))))
               'r))))]
      (app (mr om ob os 'left) 'right 'ordered)))})

(def multiply-monotone-right-spec
  {:name 'matrix/multiply-monotone-right :universes []
   :type
   (function/forall
    [['factor matrix-type] ['left matrix-type] ['right matrix-type]
     ['factor-positive (mle (mz 'factor) 'factor)]
     ['ordered (mle 'left 'right)]]
    (mle (multiply 'factor 'left)
         (multiply 'factor 'right)))
   :value
   (function/lam
    [['factor matrix-type] ['left matrix-type] ['right matrix-type]
     ['factor-positive (mle (mz 'factor) 'factor)]
     ['ordered (mle 'left 'right)]]
    (let [left-columns (transpose 'left)
          right-columns (transpose 'right)
          columns-ordered
          (app (function/const* 'matrix/transpose-monotone [])
               'left 'right 'ordered)
          m
          (function/lam
           [['rows matrix-type]]
           (function/forall
            [['positive (mle (mz 'rows) 'rows)]]
            (mle (multiply 'rows 'left)
                 (multiply 'rows 'right))))
          b
          (function/lam
           [['positive (mle (mz (nm)) (nm))]]
           trivial)
          s
          (function/lam
           [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
           (function/lam
            [['positive
              (mle (mz (cm 'row 'tail)) (cm 'row 'tail))]]
            (let [row-positive (vle (vz 'row) 'row)
                  tail-positive (mle (mz 'tail) 'tail)]
              (conjp
               (vle (action left-columns 'row)
                    (action right-columns 'row))
               (mle (multiply 'tail 'left)
                    (multiply 'tail 'right))
               (app
                (function/const*
                 'matrix/vector-multiply-monotone-rows [])
                left-columns right-columns 'row columns-ordered
                (pl row-positive tail-positive 'positive))
               (app 'ih
                    (prop-right row-positive tail-positive
                                'positive))))))]
      (app (mr m b s 'factor) 'factor-positive)))})

(def multiply-monotone-spec
  {:name 'matrix/multiply-monotone :universes []
   :type
   (function/forall
    [['source-left matrix-type] ['destination-left matrix-type]
     ['source-right matrix-type] ['destination-right matrix-type]
     ['destination-left-positive
      (mle (mz 'destination-left) 'destination-left)]
     ['source-right-positive
      (mle (mz 'source-right) 'source-right)]
     ['left-ordered (mle 'source-left 'destination-left)]
     ['right-ordered (mle 'source-right 'destination-right)]]
    (mle (multiply 'source-left 'source-right)
         (multiply 'destination-left 'destination-right)))
   :value
   (function/lam
    [['source-left matrix-type] ['destination-left matrix-type]
     ['source-right matrix-type] ['destination-right matrix-type]
     ['destination-left-positive
      (mle (mz 'destination-left) 'destination-left)]
     ['source-right-positive
      (mle (mz 'source-right) 'source-right)]
     ['left-ordered (mle 'source-left 'destination-left)]
     ['right-ordered (mle 'source-right 'destination-right)]]
    (app
     (function/const* 'matrix/at-most-transitive [])
     (multiply 'source-left 'source-right)
     (multiply 'destination-left 'source-right)
     (multiply 'destination-left 'destination-right)
     (app (function/const* 'matrix/multiply-monotone-left [])
          'source-left 'destination-left 'source-right
          'source-right-positive 'left-ordered)
     (app (function/const* 'matrix/multiply-monotone-right [])
          'destination-left 'source-right 'destination-right
          'destination-left-positive 'right-ordered)))})

(def definition-specs [])
(def theorem-specs
  [multiply-nonnegative-spec
   multiply-monotone-left-spec
   multiply-monotone-right-spec
   multiply-monotone-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.transpose-order])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-positive-multiply theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.positive-multiply))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
