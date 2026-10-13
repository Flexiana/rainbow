(ns rainbow.math.linear.matrix.antitone
  "Antitonicity of native dot products, matrix action, and multiplication.

  A fixed entrywise nonpositive vector reverses pointwise order through dot.
  Rowwise lifting gives antitonicity of matrix-vector action in either input
  when the other input is nonpositive.  Transpose then lifts those laws to
  multiplication in either factor.  Theorem-only, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.mixed-sign-multiply :as mixed-sign]
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
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- dot [a b] (app (function/const* 'vector/dot []) a b))
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

(def dot-left-antitone-spec
  {:name 'vector/dot-left-antitone :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['weights vector-type]
     ['ordered (vle 'left 'right)]
     ['weights-negative (vle 'weights (vz 'weights))]]
    (sle (dot 'right 'weights) (dot 'left 'weights)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['weights vector-type]
     ['ordered (vle 'left 'right)]
     ['weights-negative (vle 'weights (vz 'weights))]]
    (let [om
          (function/lam
           [['l vector-type]]
           (function/forall
            [['r vector-type] ['w vector-type]
             ['ord (vle 'l 'r)] ['wn (vle 'w (vz 'w))]]
            (sle (dot 'r 'w) (dot 'l 'w))))
          ob
          (let [e (nv)
                rm
                (function/lam
                 [['r vector-type]]
                 (function/forall
                  [['w vector-type] ['ord (vle e 'r)]
                   ['wn (vle 'w (vz 'w))]]
                  (sle (dot 'r 'w) (dot e 'w))))]
            (function/lam
             [['r vector-type]]
             (vr rm
                 (function/lam
                  [['w vector-type] ['ord (vle e e)]
                   ['wn (vle 'w (vz 'w))]]
                  (app (function/const* 'signed/at-most-reflexive [])
                       signed-zero))
                 (function/lam
                  [['rh signed] ['rt vector-type] ['ignored (app rm 'rt)]]
                  (function/lam
                   [['w vector-type] ['ord (vle e (cv 'rh 'rt))]
                    ['wn (vle 'w (vz 'w))]]
                   (absurd (sle (dot (cv 'rh 'rt) 'w) (dot e 'w))
                           'ord)))
                 'r)))
          os
          (function/lam
           [['lh signed] ['lt vector-type] ['ih (app om 'lt)]]
           (let [l (cv 'lh 'lt)
                 rm
                 (function/lam
                  [['r vector-type]]
                  (function/forall
                   [['w vector-type] ['ord (vle l 'r)]
                    ['wn (vle 'w (vz 'w))]]
                   (sle (dot 'r 'w) (dot l 'w))))]
             (function/lam
              [['r vector-type]]
              (vr rm
                  (function/lam
                   [['w vector-type] ['ord (vle l (nv))]
                    ['wn (vle 'w (vz 'w))]]
                   (absurd (sle (dot (nv) 'w) (dot l 'w)) 'ord))
                  (function/lam
                   [['rh signed] ['rt vector-type] ['ignored (app rm 'rt)]]
                   (let [r (cv 'rh 'rt)
                         wm
                         (function/lam
                          [['w vector-type]]
                          (function/forall
                           [['ord (vle l r)] ['wn (vle 'w (vz 'w))]]
                           (sle (dot r 'w) (dot l 'w))))]
                     (function/lam
                      [['w vector-type]]
                      (vr wm
                          (function/lam
                           [['ord (vle l r)] ['wn (vle (nv) (vz (nv)))]]
                           (app (function/const* 'signed/at-most-reflexive [])
                                signed-zero))
                          (function/lam
                           [['wh signed] ['wt vector-type]
                            ['ignored (app wm 'wt)]]
                           (function/lam
                            [['ord (vle l r)]
                             ['wn (vle (cv 'wh 'wt)
                                       (vz (cv 'wh 'wt)))]]
                            (let [ho (sle 'lh 'rh) to (vle 'lt 'rt)
                                  hw (sle 'wh signed-zero)
                                  tw (vle 'wt (vz 'wt))]
                              (app (function/const* 'signed/add-monotone [])
                                   (smul 'rh 'wh) (smul 'lh 'wh)
                                   (dot 'rt 'wt) (dot 'lt 'wt)
                                   (app
                                    (function/const*
                                     'signed/multiply-right-antitone [])
                                    'wh 'lh 'rh
                                    (pl hw tw 'wn) (pl ho to 'ord))
                                   (app 'ih 'rt 'wt
                                        (prop-right ho to 'ord)
                                        (prop-right hw tw 'wn))))))
                          'w))))
                  'r))))]
      (app (vr om ob os 'left) 'right 'weights
           'ordered 'weights-negative)))})

(def dot-right-antitone-spec
  {:name 'vector/dot-right-antitone :universes []
   :type
   (function/forall
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['weights-negative (vle 'weights (vz 'weights))]
     ['ordered (vle 'left 'right)]]
    (sle (dot 'weights 'right) (dot 'weights 'left)))
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['weights-negative (vle 'weights (vz 'weights))]
     ['ordered (vle 'left 'right)]]
    (app (function/const* 'signed/at-most-respects-equivalence [])
         (dot 'right 'weights) (dot 'weights 'right)
         (dot 'left 'weights) (dot 'weights 'left)
         (app (function/const* 'vector/dot-commutative [])
              'right 'weights)
         (app (function/const* 'vector/dot-commutative [])
              'left 'weights)
         (app (function/const* 'vector/dot-left-antitone [])
              'left 'right 'weights 'ordered 'weights-negative)))})

(def action-antitone-values-spec
  {:name 'matrix/vector-multiply-antitone-values :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['rows-negative (mle 'rows (mz 'rows))]
     ['ordered (vle 'left 'right)]]
    (vle (action 'rows 'right) (action 'rows 'left)))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['rows-negative (mle 'rows (mz 'rows))]
     ['ordered (vle 'left 'right)]]
    (let [m
          (function/lam
           [['rs matrix-type]]
           (function/forall
            [['rn (mle 'rs (mz 'rs))]]
            (vle (action 'rs 'right) (action 'rs 'left))))
          b (function/lam [['rn (mle (nm) (mz (nm)))]] trivial)
          s
          (function/lam
           [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
           (function/lam
            [['rn (mle (cm 'row 'tail) (mz (cm 'row 'tail)))]]
            (let [hr (vle 'row (vz 'row)) tr (mle 'tail (mz 'tail))]
              (conjp
               (sle (dot 'row 'right) (dot 'row 'left))
               (vle (action 'tail 'right) (action 'tail 'left))
               (app (function/const* 'vector/dot-right-antitone [])
                    'row 'left 'right (pl hr tr 'rn) 'ordered)
               (app 'ih (prop-right hr tr 'rn))))))]
      (app (mr m b s 'rows) 'rows-negative)))})

(def action-antitone-rows-spec
  {:name 'matrix/vector-multiply-antitone-rows :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['ordered (mle 'left 'right)]
     ['values-negative (vle 'values (vz 'values))]]
    (vle (action 'right 'values) (action 'left 'values)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['ordered (mle 'left 'right)]
     ['values-negative (vle 'values (vz 'values))]]
    (let [om
          (function/lam
           [['l matrix-type]]
           (function/forall
            [['r matrix-type] ['ord (mle 'l 'r)]]
            (vle (action 'r 'values) (action 'l 'values))))
          ob
          (let [e (nm)
                rm (function/lam [['r matrix-type]]
                     (function/forall [['ord (mle e 'r)]]
                                      (vle (action 'r 'values)
                                           (action e 'values))))]
            (function/lam
             [['r matrix-type]]
             (mr rm
                 (function/lam [['ord (mle e e)]] trivial)
                 (function/lam
                  [['rh vector-type] ['rt matrix-type] ['ignored (app rm 'rt)]]
                  (function/lam [['ord (mle e (cm 'rh 'rt))]]
                                (absurd (vle (action (cm 'rh 'rt) 'values)
                                             (action e 'values))
                                        'ord)))
                 'r)))
          os
          (function/lam
           [['lh vector-type] ['lt matrix-type] ['ih (app om 'lt)]]
           (let [l (cm 'lh 'lt)
                 rm (function/lam [['r matrix-type]]
                      (function/forall [['ord (mle l 'r)]]
                                       (vle (action 'r 'values)
                                            (action l 'values))))]
             (function/lam
              [['r matrix-type]]
              (mr rm
                  (function/lam [['ord (mle l (nm))]]
                                (absurd (vle (action (nm) 'values)
                                             (action l 'values)) 'ord))
                  (function/lam
                   [['rh vector-type] ['rt matrix-type] ['ignored (app rm 'rt)]]
                   (function/lam
                    [['ord (mle l (cm 'rh 'rt))]]
                    (let [ho (vle 'lh 'rh) to (mle 'lt 'rt)]
                      (conjp
                       (sle (dot 'rh 'values) (dot 'lh 'values))
                       (vle (action 'rt 'values) (action 'lt 'values))
                       (app (function/const* 'vector/dot-left-antitone [])
                            'lh 'rh 'values
                            (pl ho to 'ord) 'values-negative)
                       (app 'ih 'rt (prop-right ho to 'ord))))))
                  'r))))]
      (app (mr om ob os 'left) 'right 'ordered)))})

(def action-antitone-spec
  {:name 'matrix/vector-multiply-antitone :universes []
   :type
   (function/forall
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['destination-rows-negative
      (mle 'destination-rows (mz 'destination-rows))]
     ['source-values-negative
      (vle 'source-values (vz 'source-values))]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (vle (action 'destination-rows 'destination-values)
         (action 'source-rows 'source-values)))
   :value
   (function/lam
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['destination-rows-negative
      (mle 'destination-rows (mz 'destination-rows))]
     ['source-values-negative
      (vle 'source-values (vz 'source-values))]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (app (function/const* 'vector/at-most-transitive [])
         (action 'destination-rows 'destination-values)
         (action 'destination-rows 'source-values)
         (action 'source-rows 'source-values)
         (app
          (function/const* 'matrix/vector-multiply-antitone-values [])
          'destination-rows 'source-values 'destination-values
          'destination-rows-negative 'values-ordered)
         (app
          (function/const* 'matrix/vector-multiply-antitone-rows [])
          'source-rows 'destination-rows 'source-values
          'rows-ordered 'source-values-negative)))})

(def multiply-antitone-left-spec
  {:name 'matrix/multiply-antitone-left :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['factor matrix-type]
     ['factor-negative (mle 'factor (mz 'factor))]
     ['ordered (mle 'left 'right)]]
    (mle (multiply 'right 'factor)
         (multiply 'left 'factor)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['factor matrix-type]
     ['factor-negative (mle 'factor (mz 'factor))]
     ['ordered (mle 'left 'right)]]
    (let [columns (transpose 'factor)
          columns-negative
          (app (function/const* 'matrix/transpose-nonpositive [])
               'factor 'factor-negative)
          om
          (function/lam
           [['l matrix-type]]
           (function/forall
            [['r matrix-type] ['ord (mle 'l 'r)]]
            (mle (multiply 'r 'factor)
                 (multiply 'l 'factor))))
          ob
          (let [e (nm)
                rm
                (function/lam
                 [['r matrix-type]]
                 (function/forall
                  [['ord (mle e 'r)]]
                  (mle (multiply 'r 'factor)
                       (multiply e 'factor))))]
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
                 (mle (multiply (cm 'row 'tail) 'factor)
                      (multiply e 'factor))
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
                   (mle (multiply 'r 'factor)
                        (multiply l 'factor))))]
             (function/lam
              [['r matrix-type]]
              (mr
               rm
               (function/lam
                [['ord (mle l (nm))]]
                (absurd
                 (mle (multiply (nm) 'factor)
                      (multiply l 'factor))
                 'ord))
               (function/lam
                [['rrow vector-type] ['rtail matrix-type]
                 ['ignored (app rm 'rtail)]]
                (function/lam
                 [['ord (mle l (cm 'rrow 'rtail))]]
                 (let [row-order (vle 'lrow 'rrow)
                       tail-order (mle 'ltail 'rtail)]
                   (conjp
                    (vle (action columns 'rrow)
                         (action columns 'lrow))
                    (mle (multiply 'rtail 'factor)
                         (multiply 'ltail 'factor))
                    (app
                     (function/const*
                      'matrix/vector-multiply-antitone-values [])
                     columns 'lrow 'rrow columns-negative
                     (pl row-order tail-order 'ord))
                    (app 'ih 'rtail
                         (prop-right row-order tail-order 'ord))))))
               'r))))]
      (app (mr om ob os 'left) 'right 'ordered)))})

(def multiply-antitone-right-spec
  {:name 'matrix/multiply-antitone-right :universes []
   :type
   (function/forall
    [['factor matrix-type] ['left matrix-type] ['right matrix-type]
     ['factor-negative (mle 'factor (mz 'factor))]
     ['ordered (mle 'left 'right)]]
    (mle (multiply 'factor 'right)
         (multiply 'factor 'left)))
   :value
   (function/lam
    [['factor matrix-type] ['left matrix-type] ['right matrix-type]
     ['factor-negative (mle 'factor (mz 'factor))]
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
            [['negative (mle 'rows (mz 'rows))]]
            (mle (multiply 'rows 'right)
                 (multiply 'rows 'left))))
          b
          (function/lam
           [['negative (mle (nm) (mz (nm)))]]
           trivial)
          s
          (function/lam
           [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
           (function/lam
            [['negative
              (mle (cm 'row 'tail) (mz (cm 'row 'tail)))]]
            (let [row-negative (vle 'row (vz 'row))
                  tail-negative (mle 'tail (mz 'tail))]
              (conjp
               (vle (action right-columns 'row)
                    (action left-columns 'row))
               (mle (multiply 'tail 'right)
                    (multiply 'tail 'left))
               (app
                (function/const*
                 'matrix/vector-multiply-antitone-rows [])
                left-columns right-columns 'row columns-ordered
                (pl row-negative tail-negative 'negative))
               (app 'ih
                    (prop-right row-negative tail-negative
                                'negative))))))]
      (app (mr m b s 'factor) 'factor-negative)))})

(def multiply-antitone-spec
  {:name 'matrix/multiply-antitone :universes []
   :type
   (function/forall
    [['source-left matrix-type] ['destination-left matrix-type]
     ['source-right matrix-type] ['destination-right matrix-type]
     ['destination-left-negative
      (mle 'destination-left (mz 'destination-left))]
     ['source-right-negative
      (mle 'source-right (mz 'source-right))]
     ['left-ordered (mle 'source-left 'destination-left)]
     ['right-ordered (mle 'source-right 'destination-right)]]
    (mle (multiply 'destination-left 'destination-right)
         (multiply 'source-left 'source-right)))
   :value
   (function/lam
    [['source-left matrix-type] ['destination-left matrix-type]
     ['source-right matrix-type] ['destination-right matrix-type]
     ['destination-left-negative
      (mle 'destination-left (mz 'destination-left))]
     ['source-right-negative
      (mle 'source-right (mz 'source-right))]
     ['left-ordered (mle 'source-left 'destination-left)]
     ['right-ordered (mle 'source-right 'destination-right)]]
    (app
     (function/const* 'matrix/at-most-transitive [])
     (multiply 'destination-left 'destination-right)
     (multiply 'destination-left 'source-right)
     (multiply 'source-left 'source-right)
     (app (function/const* 'matrix/multiply-antitone-right [])
          'destination-left 'source-right 'destination-right
          'destination-left-negative 'right-ordered)
     (app (function/const* 'matrix/multiply-antitone-left [])
          'source-left 'destination-left 'source-right
          'source-right-negative 'left-ordered)))})

(def definition-specs [])
(def theorem-specs
  [dot-left-antitone-spec
   dot-right-antitone-spec
   action-antitone-values-spec
   action-antitone-rows-spec
   action-antitone-spec
   multiply-antitone-left-spec
   multiply-antitone-right-spec
   multiply-antitone-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.mixed-sign-multiply])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-antitone theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.antitone))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
