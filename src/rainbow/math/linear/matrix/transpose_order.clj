(ns rainbow.math.linear.matrix.transpose-order
  "Pointwise order and nonnegativity for total native matrix transpose.

  Column insertion preserves entrywise nonnegativity and is jointly monotone
  in its vector and matrix inputs.  Structural lifting through the reducible
  total transpose then proves that transpose preserves both zero lower bounds
  and matrix pointwise order, including the established ragged semantics.
  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.positive-action :as action]
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
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- prepend [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- conjp [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- pl [a b p]
  (app (function/const* 'proposition/left []) a b p))
(defn- prop-right [a b p]
  (app (function/const* 'proposition/right []) a b p))
(defn- absurd [goal bad] (app bad goal))

(def prepend-column-nonnegative-spec
  {:name 'matrix/prepend-column-nonnegative :universes []
   :type
   (function/forall
    [['values vector-type] ['columns matrix-type]
     ['values-positive (vle (vz 'values) 'values)]
     ['columns-positive (mle (mz 'columns) 'columns)]]
    (mle (mz (prepend 'values 'columns))
         (prepend 'values 'columns)))
   :value
   (function/lam
    [['values vector-type] ['columns matrix-type]
     ['values-positive (vle (vz 'values) 'values)]
     ['columns-positive (mle (mz 'columns) 'columns)]]
    (let [m
          (function/lam
           [['vs vector-type]]
           (function/forall
            [['cs matrix-type]
             ['vp (vle (vz 'vs) 'vs)]
             ['cp (mle (mz 'cs) 'cs)]]
            (mle (mz (prepend 'vs 'cs)) (prepend 'vs 'cs))))
          b
          (function/lam
           [['cs matrix-type]
            ['vp (vle (vz (nv)) (nv))]
            ['cp (mle (mz 'cs) 'cs)]]
           trivial)
          s
          (function/lam
           [['h signed] ['tail vector-type] ['ih (app m 'tail)]]
           (let [vs (cv 'h 'tail)
                 cmotive
                 (function/lam
                  [['cs matrix-type]]
                  (function/forall
                   [['vp (vle (vz vs) vs)]
                    ['cp (mle (mz 'cs) 'cs)]]
                   (mle (mz (prepend vs 'cs))
                        (prepend vs 'cs))))]
             (function/lam
              [['cs matrix-type]]
              (mr
               cmotive
               (function/lam
                [['vp (vle (vz vs) vs)]
                 ['cp (mle (mz (nm)) (nm))]]
                (let [hp (sle signed-zero 'h)
                      tp (vle (vz 'tail) 'tail)
                      singleton (cv 'h (nv))]
                  (conjp
                   (vle (vz singleton) singleton)
                   (mle (mz (prepend 'tail (nm)))
                        (prepend 'tail (nm)))
                   (conjp hp (vle (vz (nv)) (nv))
                          (pl hp tp 'vp) trivial)
                   (app 'ih (nm) (prop-right hp tp 'vp) trivial))))
               (function/lam
                [['col vector-type] ['cols matrix-type]
                 ['ignored (app cmotive 'cols)]]
                (function/lam
                 [['vp (vle (vz vs) vs)]
                  ['cp (mle (mz (cm 'col 'cols))
                           (cm 'col 'cols))]]
                 (let [hp (sle signed-zero 'h)
                       tp (vle (vz 'tail) 'tail)
                       colp (vle (vz 'col) 'col)
                       colsp (mle (mz 'cols) 'cols)
                       row (cv 'h 'col)]
                   (conjp
                    (vle (vz row) row)
                    (mle (mz (prepend 'tail 'cols))
                         (prepend 'tail 'cols))
                    (conjp hp colp
                           (pl hp tp 'vp)
                           (pl colp colsp 'cp))
                    (app 'ih 'cols
                         (prop-right hp tp 'vp)
                         (prop-right colp colsp 'cp))))))
               'cs))))]
      (app (vr m b s 'values)
           'columns 'values-positive 'columns-positive)))})

(def prepend-column-monotone-spec
  {:name 'matrix/prepend-column-monotone :universes []
   :type
   (function/forall
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-ordered (vle 'left-values 'right-values)]
     ['columns-ordered (mle 'left-columns 'right-columns)]]
    (mle (prepend 'left-values 'left-columns)
         (prepend 'right-values 'right-columns)))
   :value
   (function/lam
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-ordered (vle 'left-values 'right-values)]
     ['columns-ordered (mle 'left-columns 'right-columns)]]
    (let [om
          (function/lam
           [['lv vector-type]]
           (function/forall
            [['rv vector-type] ['lc matrix-type] ['rc matrix-type]
             ['vo (vle 'lv 'rv)] ['co (mle 'lc 'rc)]]
            (mle (prepend 'lv 'lc) (prepend 'rv 'rc))))
          ob
          (let [lv (nv)
                rm
                (function/lam
                 [['rv vector-type]]
                 (function/forall
                  [['lc matrix-type] ['rc matrix-type]
                   ['vo (vle lv 'rv)] ['co (mle 'lc 'rc)]]
                  (mle (prepend lv 'lc) (prepend 'rv 'rc))))]
            (function/lam
             [['rv vector-type]]
             (vr
              rm
              (function/lam
               [['lc matrix-type] ['rc matrix-type]
                ['vo (vle lv lv)] ['co (mle 'lc 'rc)]]
               trivial)
              (function/lam
               [['rh signed] ['rt vector-type] ['ignored (app rm 'rt)]]
               (function/lam
                [['lc matrix-type] ['rc matrix-type]
                 ['vo (vle lv (cv 'rh 'rt))]
                 ['co (mle 'lc 'rc)]]
                (absurd
                 (mle (prepend lv 'lc)
                      (prepend (cv 'rh 'rt) 'rc))
                 'vo)))
              'rv)))
          os
          (function/lam
           [['lh signed] ['lt vector-type] ['ih (app om 'lt)]]
           (let [lv (cv 'lh 'lt)
                 rm
                 (function/lam
                  [['rv vector-type]]
                  (function/forall
                   [['lc matrix-type] ['rc matrix-type]
                    ['vo (vle lv 'rv)] ['co (mle 'lc 'rc)]]
                   (mle (prepend lv 'lc) (prepend 'rv 'rc))))]
             (function/lam
              [['rv vector-type]]
              (vr
               rm
               (function/lam
                [['lc matrix-type] ['rc matrix-type]
                 ['vo (vle lv (nv))] ['co (mle 'lc 'rc)]]
                (absurd
                 (mle (prepend lv 'lc) (prepend (nv) 'rc))
                 'vo))
               (function/lam
                [['rh signed] ['rt vector-type] ['ignored (app rm 'rt)]]
                (function/lam
                 [['lc matrix-type] ['rc matrix-type]
                  ['vo (vle lv (cv 'rh 'rt))]
                  ['co (mle 'lc 'rc)]]
                 (let [ho (sle 'lh 'rh)
                       to (vle 'lt 'rt)
                       lm
                       (function/lam
                        [['current-lc matrix-type]]
                        (function/forall
                         [['current-rc matrix-type]
                          ['current-co (mle 'current-lc 'current-rc)]]
                         (mle (prepend lv 'current-lc)
                              (prepend (cv 'rh 'rt) 'current-rc))))]
                   (app
                    (mr
                     lm
                     (let [lc (nm)
                           rcm
                           (function/lam
                            [['current-rc matrix-type]]
                            (function/forall
                             [['current-co (mle lc 'current-rc)]]
                             (mle (prepend lv lc)
                                  (prepend (cv 'rh 'rt) 'current-rc))))]
                       (function/lam
                        [['current-rc matrix-type]]
                        (mr
                         rcm
                         (function/lam
                          [['current-co (mle lc (nm))]]
                          (let [left-row (cv 'lh (nv))
                                right-row (cv 'rh (nv))]
                            (conjp
                             (vle left-row right-row)
                             (mle (prepend 'lt (nm))
                                  (prepend 'rt (nm)))
                             (conjp ho (vle (nv) (nv))
                                    (pl ho to 'vo) trivial)
                             (app 'ih 'rt (nm) (nm)
                                  (prop-right ho to 'vo) trivial))))
                         (function/lam
                          [['rcol vector-type] ['rcols matrix-type]
                           ['ignored (app rcm 'rcols)]]
                          (function/lam
                           [['current-co
                             (mle lc (cm 'rcol 'rcols))]]
                           (absurd
                            (mle (prepend lv lc)
                                 (prepend (cv 'rh 'rt)
                                          (cm 'rcol 'rcols)))
                            'current-co)))
                         'current-rc)))
                     (function/lam
                      [['lcol vector-type] ['lcols matrix-type]
                       ['ignored (app lm 'lcols)]]
                      (let [lc (cm 'lcol 'lcols)
                            rcm
                            (function/lam
                             [['current-rc matrix-type]]
                             (function/forall
                              [['current-co (mle lc 'current-rc)]]
                              (mle (prepend lv lc)
                                   (prepend (cv 'rh 'rt) 'current-rc))))]
                        (function/lam
                         [['current-rc matrix-type]]
                         (mr
                          rcm
                          (function/lam
                           [['current-co (mle lc (nm))]]
                           (absurd
                            (mle (prepend lv lc)
                                 (prepend (cv 'rh 'rt) (nm)))
                            'current-co))
                          (function/lam
                           [['rcol vector-type] ['rcols matrix-type]
                            ['ignored (app rcm 'rcols)]]
                           (function/lam
                            [['current-co
                              (mle lc (cm 'rcol 'rcols))]]
                            (let [col-order (vle 'lcol 'rcol)
                                  cols-order (mle 'lcols 'rcols)
                                  left-row (cv 'lh 'lcol)
                                  right-row (cv 'rh 'rcol)]
                              (conjp
                               (vle left-row right-row)
                               (mle (prepend 'lt 'lcols)
                                    (prepend 'rt 'rcols))
                               (conjp ho col-order
                                      (pl ho to 'vo)
                                      (pl col-order cols-order
                                          'current-co))
                               (app 'ih 'rt 'lcols 'rcols
                                    (prop-right ho to 'vo)
                                    (prop-right col-order cols-order
                                        'current-co))))))
                          'current-rc))))
                     'lc)
                    'rc 'co))))
               'rv))))]
      (app (vr om ob os 'left-values)
           'right-values 'left-columns 'right-columns
           'values-ordered 'columns-ordered)))})

(def transpose-nonnegative-spec
  {:name 'matrix/transpose-nonnegative :universes []
   :type
   (function/forall
    [['rows matrix-type]
     ['positive (mle (mz 'rows) 'rows)]]
    (mle (mz (transpose 'rows)) (transpose 'rows)))
   :value
   (function/lam
    [['rows matrix-type]
     ['positive (mle (mz 'rows) 'rows)]]
    (let [m
          (function/lam
           [['rs matrix-type]]
           (function/forall
            [['rp (mle (mz 'rs) 'rs)]]
            (mle (mz (transpose 'rs)) (transpose 'rs))))
          b
          (function/lam
           [['rp (mle (mz (nm)) (nm))]]
           trivial)
          s
          (function/lam
           [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
           (function/lam
            [['rp (mle (mz (cm 'row 'tail)) (cm 'row 'tail))]]
            (let [rowp (vle (vz 'row) 'row)
                  tailp (mle (mz 'tail) 'tail)]
              (app (function/const* 'matrix/prepend-column-nonnegative [])
                   'row (transpose 'tail)
                   (pl rowp tailp 'rp)
                   (app 'ih (prop-right rowp tailp 'rp))))))]
      (app (mr m b s 'rows) 'positive)))})

(def transpose-monotone-spec
  {:name 'matrix/transpose-monotone :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['ordered (mle 'left 'right)]]
    (mle (transpose 'left) (transpose 'right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['ordered (mle 'left 'right)]]
    (let [om
          (function/lam
           [['l matrix-type]]
           (function/forall
            [['r matrix-type] ['ord (mle 'l 'r)]]
            (mle (transpose 'l) (transpose 'r))))
          ob
          (let [e (nm)
                rm
                (function/lam
                 [['r matrix-type]]
                 (function/forall
                  [['ord (mle e 'r)]]
                  (mle (transpose e) (transpose 'r))))]
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
                 (mle (transpose e)
                      (transpose (cm 'row 'tail)))
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
                   (mle (transpose l) (transpose 'r))))]
             (function/lam
              [['r matrix-type]]
              (mr
               rm
               (function/lam
                [['ord (mle l (nm))]]
                (absurd
                 (mle (transpose l) (transpose (nm)))
                 'ord))
               (function/lam
                [['rrow vector-type] ['rtail matrix-type]
                 ['ignored (app rm 'rtail)]]
                (function/lam
                 [['ord (mle l (cm 'rrow 'rtail))]]
                 (let [row-order (vle 'lrow 'rrow)
                       tail-order (mle 'ltail 'rtail)]
                   (app (function/const* 'matrix/prepend-column-monotone [])
                        'lrow 'rrow
                        (transpose 'ltail) (transpose 'rtail)
                        (pl row-order tail-order 'ord)
                        (app 'ih 'rtail
                             (prop-right row-order tail-order 'ord))))))
               'r))))]
      (app (mr om ob os 'left) 'right 'ordered)))})

(def definition-specs [])
(def theorem-specs
  [prepend-column-nonnegative-spec
   prepend-column-monotone-spec
   transpose-nonnegative-spec
   transpose-monotone-spec])

(defn extend-environment [env]
  (-> env
      action/extend-environment
      (support/extend-with :finite-matrix-transpose-order theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
