(ns rainbow.math.linear.matrix.mixed-sign-multiply
  "Mixed-sign laws for native finite matrix multiplication.

  Column insertion and total transpose preserve entrywise nonpositivity.  The
  mixed-sign matrix-action laws then lift rowwise to products: a nonpositive
  factor times a nonnegative factor is entrywise nonpositive in either factor
  order, while two nonpositive factors yield an entrywise nonnegative product.
  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.mixed-sign-action :as mixed-action]
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
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- vz [values] (app (function/const* 'vector/zero-like []) values))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- mz [rows] (app (function/const* 'matrix/zero-like []) rows))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- prepend [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
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
(defn- vector-sign [nonnegative? values]
  (if nonnegative?
    (vle (vz values) values)
    (vle values (vz values))))
(defn- matrix-sign [nonnegative? rows]
  (if nonnegative?
    (mle (mz rows) rows)
    (mle rows (mz rows))))

(def prepend-column-nonpositive-spec
  {:name 'matrix/prepend-column-nonpositive :universes []
   :type
   (function/forall
    [['values vector-type] ['columns matrix-type]
     ['values-negative (vle 'values (vz 'values))]
     ['columns-negative (mle 'columns (mz 'columns))]]
    (mle (prepend 'values 'columns)
         (mz (prepend 'values 'columns))))
   :value
   (function/lam
    [['values vector-type] ['columns matrix-type]
     ['values-negative (vle 'values (vz 'values))]
     ['columns-negative (mle 'columns (mz 'columns))]]
    (let [m
          (function/lam
           [['vs vector-type]]
           (function/forall
            [['cs matrix-type]
             ['vn (vle 'vs (vz 'vs))]
             ['cn (mle 'cs (mz 'cs))]]
            (mle (prepend 'vs 'cs) (mz (prepend 'vs 'cs)))))
          b
          (function/lam
           [['cs matrix-type]
            ['vn (vle (nv) (vz (nv)))]
            ['cn (mle 'cs (mz 'cs))]]
           trivial)
          s
          (function/lam
           [['h signed] ['tail vector-type] ['ih (app m 'tail)]]
           (let [vs (cv 'h 'tail)
                 cmotive
                 (function/lam
                  [['cs matrix-type]]
                  (function/forall
                   [['vn (vle vs (vz vs))]
                    ['cn (mle 'cs (mz 'cs))]]
                   (mle (prepend vs 'cs)
                        (mz (prepend vs 'cs)))))]
             (function/lam
              [['cs matrix-type]]
              (mr
               cmotive
               (function/lam
                [['vn (vle vs (vz vs))]
                 ['cn (mle (nm) (mz (nm)))]]
                (let [hn (sle 'h signed-zero)
                      tn (vle 'tail (vz 'tail))
                      singleton (cv 'h (nv))]
                  (conjp
                   (vle singleton (vz singleton))
                   (mle (prepend 'tail (nm))
                        (mz (prepend 'tail (nm))))
                   (conjp hn (vle (nv) (vz (nv)))
                          (pl hn tn 'vn) trivial)
                   (app 'ih (nm) (prop-right hn tn 'vn) trivial))))
               (function/lam
                [['col vector-type] ['cols matrix-type]
                 ['ignored (app cmotive 'cols)]]
                (function/lam
                 [['vn (vle vs (vz vs))]
                  ['cn (mle (cm 'col 'cols) (mz (cm 'col 'cols)))]]
                 (let [hn (sle 'h signed-zero)
                       tn (vle 'tail (vz 'tail))
                       coln (vle 'col (vz 'col))
                       colsn (mle 'cols (mz 'cols))
                       row (cv 'h 'col)]
                   (conjp
                    (vle row (vz row))
                    (mle (prepend 'tail 'cols)
                         (mz (prepend 'tail 'cols)))
                    (conjp hn coln
                           (pl hn tn 'vn)
                           (pl coln colsn 'cn))
                    (app 'ih 'cols
                         (prop-right hn tn 'vn)
                         (prop-right coln colsn 'cn))))))
               'cs))))]
      (app (vr m b s 'values)
           'columns 'values-negative 'columns-negative)))})

(def transpose-nonpositive-spec
  {:name 'matrix/transpose-nonpositive :universes []
   :type
   (function/forall
    [['rows matrix-type]
     ['negative (mle 'rows (mz 'rows))]]
    (mle (transpose 'rows) (mz (transpose 'rows))))
   :value
   (function/lam
    [['rows matrix-type]
     ['negative (mle 'rows (mz 'rows))]]
    (let [m
          (function/lam
           [['rs matrix-type]]
           (function/forall
            [['rn (mle 'rs (mz 'rs))]]
            (mle (transpose 'rs) (mz (transpose 'rs)))))
          b
          (function/lam [['rn (mle (nm) (mz (nm)))]] trivial)
          s
          (function/lam
           [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
           (function/lam
            [['rn (mle (cm 'row 'tail) (mz (cm 'row 'tail)))]]
            (let [rown (vle 'row (vz 'row))
                  tailn (mle 'tail (mz 'tail))]
              (app (function/const* 'matrix/prepend-column-nonpositive [])
                   'row (transpose 'tail)
                   (pl rown tailn 'rn)
                   (app 'ih (prop-right rown tailn 'rn))))))]
      (app (mr m b s 'rows) 'negative)))})

(defn- multiply-sign-lift
  [action-theorem left-nonnegative? right-nonnegative? result-nonnegative?]
  (function/lam
   [['left matrix-type] ['right matrix-type]
    ['left-sign (matrix-sign left-nonnegative? 'left)]
    ['right-sign (matrix-sign right-nonnegative? 'right)]]
   (let [columns (transpose 'right)
         columns-sign
         (app
          (function/const*
           (if right-nonnegative?
             'matrix/transpose-nonnegative
             'matrix/transpose-nonpositive)
           [])
          'right 'right-sign)
         m
         (function/lam
          [['rows matrix-type]]
          (function/forall
           [['rows-sign (matrix-sign left-nonnegative? 'rows)]]
           (matrix-sign result-nonnegative? (multiply 'rows 'right))))
         b
         (function/lam
          [['rows-sign (matrix-sign left-nonnegative? (nm))]]
          trivial)
         s
         (function/lam
          [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
          (function/lam
           [['rows-sign
             (matrix-sign left-nonnegative? (cm 'row 'tail))]]
           (let [row-sign (vector-sign left-nonnegative? 'row)
                 tail-sign (matrix-sign left-nonnegative? 'tail)]
             (conjp
              (vector-sign result-nonnegative? (action columns 'row))
              (matrix-sign result-nonnegative? (multiply 'tail 'right))
              (app (function/const* action-theorem [])
                   columns 'row columns-sign
                   (pl row-sign tail-sign 'rows-sign))
              (app 'ih (prop-right row-sign tail-sign 'rows-sign))))))]
     (app (mr m b s 'left) 'left-sign))))

(def multiply-nonpositive-left-spec
  {:name 'matrix/multiply-nonpositive-left :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['left-negative (mle 'left (mz 'left))]
     ['right-positive (mle (mz 'right) 'right)]]
    (mle (multiply 'left 'right) (mz (multiply 'left 'right))))
   :value
   (multiply-sign-lift
    'matrix/vector-multiply-nonpositive-values false true false)})

(def multiply-nonpositive-right-spec
  {:name 'matrix/multiply-nonpositive-right :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['left-positive (mle (mz 'left) 'left)]
     ['right-negative (mle 'right (mz 'right))]]
    (mle (multiply 'left 'right) (mz (multiply 'left 'right))))
   :value
   (multiply-sign-lift
    'matrix/vector-multiply-nonpositive-rows true false false)})

(def multiply-nonnegative-both-nonpositive-spec
  {:name 'matrix/multiply-nonnegative-both-nonpositive :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['left-negative (mle 'left (mz 'left))]
     ['right-negative (mle 'right (mz 'right))]]
    (mle (mz (multiply 'left 'right)) (multiply 'left 'right)))
   :value
   (multiply-sign-lift
    'matrix/vector-multiply-nonnegative-both-nonpositive
    false false true)})

(def definition-specs [])
(def theorem-specs
  [prepend-column-nonpositive-spec
   transpose-nonpositive-spec
   multiply-nonpositive-left-spec
   multiply-nonpositive-right-spec
   multiply-nonnegative-both-nonpositive-spec])

(defn extend-environment [env]
  (-> env
      mixed-action/extend-environment
      (support/extend-with :finite-matrix-mixed-sign-multiply theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
