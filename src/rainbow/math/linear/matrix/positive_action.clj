(ns rainbow.math.linear.matrix.positive-action
  "Positive dot products and monotone native matrix-vector action.

  A dot product is monotone in either argument when the fixed argument is
  entrywise nonnegative, hence two nonnegative vectors have a nonnegative dot.
  Rowwise lifting proves that matrix-vector action is nonnegative and monotone
  in its matrix, vector, or both inputs under the corresponding zero lower
  bounds.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.signed-scale-sign :as sign]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.order-monotone :as order-monotone]))

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
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- vme [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- dot [a b] (app (function/const* 'vector/dot []) a b))
(defn- action [a b]
  (app (function/const* 'matrix/vector-multiply []) a b))
(defn- conjp [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- pl [a b p] (app (function/const* 'proposition/left []) a b p))
(defn- prop-right [a b p]
  (app (function/const* 'proposition/right []) a b p))
(defn- absurd [goal bad] (app bad goal))

(def dot-left-monotone-spec
  {:name 'vector/dot-left-monotone :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['weights vector-type]
     ['ordered (vle 'left 'right)]
     ['weights-positive (vle (vz 'weights) 'weights)]]
    (sle (dot 'left 'weights) (dot 'right 'weights)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['weights vector-type]
     ['ordered (vle 'left 'right)]
     ['weights-positive (vle (vz 'weights) 'weights)]]
    (let [om
          (function/lam
           [['l vector-type]]
           (function/forall
            [['r vector-type] ['w vector-type]
             ['ord (vle 'l 'r)] ['wp (vle (vz 'w) 'w)]]
            (sle (dot 'l 'w) (dot 'r 'w))))
          ob
          (let [e (nv)
                rm
                (function/lam
                 [['r vector-type]]
                 (function/forall
                  [['w vector-type] ['ord (vle e 'r)]
                   ['wp (vle (vz 'w) 'w)]]
                  (sle (dot e 'w) (dot 'r 'w))))]
            (function/lam
             [['r vector-type]]
             (vr rm
                 (function/lam
                  [['w vector-type] ['ord (vle e e)]
                   ['wp (vle (vz 'w) 'w)]]
                  (app (function/const* 'signed/at-most-reflexive [])
                       signed-zero))
                 (function/lam
                  [['rh signed] ['rt vector-type] ['ignored (app rm 'rt)]]
                  (function/lam
                   [['w vector-type] ['ord (vle e (cv 'rh 'rt))]
                    ['wp (vle (vz 'w) 'w)]]
                   (absurd (sle (dot e 'w) (dot (cv 'rh 'rt) 'w))
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
                    ['wp (vle (vz 'w) 'w)]]
                   (sle (dot l 'w) (dot 'r 'w))))]
             (function/lam
              [['r vector-type]]
              (vr rm
                  (function/lam
                   [['w vector-type] ['ord (vle l (nv))]
                    ['wp (vle (vz 'w) 'w)]]
                   (absurd (sle (dot l 'w) (dot (nv) 'w)) 'ord))
                  (function/lam
                   [['rh signed] ['rt vector-type] ['ignored (app rm 'rt)]]
                   (let [r (cv 'rh 'rt)
                         wm
                         (function/lam
                          [['w vector-type]]
                          (function/forall
                           [['ord (vle l r)] ['wp (vle (vz 'w) 'w)]]
                           (sle (dot l 'w) (dot r 'w))))]
                     (function/lam
                      [['w vector-type]]
                      (vr wm
                          (function/lam
                           [['ord (vle l r)] ['wp (vle (vz (nv)) (nv))]]
                           (app (function/const* 'signed/at-most-reflexive [])
                                signed-zero))
                          (function/lam
                           [['wh signed] ['wt vector-type]
                            ['ignored (app wm 'wt)]]
                           (function/lam
                            [['ord (vle l r)]
                             ['wp (vle (vz (cv 'wh 'wt)) (cv 'wh 'wt))]]
                            (let [ho (sle 'lh 'rh) to (vle 'lt 'rt)
                                  hw (sle signed-zero 'wh)
                                  tw (vle (vz 'wt) 'wt)]
                              (app (function/const* 'signed/add-monotone [])
                                   (smul 'lh 'wh) (smul 'rh 'wh)
                                   (dot 'lt 'wt) (dot 'rt 'wt)
                                   (app
                                    (function/const*
                                     'signed/multiply-right-monotone [])
                                    'wh 'lh 'rh
                                    (pl hw tw 'wp) (pl ho to 'ord))
                                   (app 'ih 'rt 'wt
                                        (prop-right ho to 'ord)
                                        (prop-right hw tw 'wp))))))
                          'w))))
                  'r))))]
      (app (vr om ob os 'left) 'right 'weights
           'ordered 'weights-positive)))})

(def dot-right-monotone-spec
  {:name 'vector/dot-right-monotone :universes []
   :type
   (function/forall
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['weights-positive (vle (vz 'weights) 'weights)]
     ['ordered (vle 'left 'right)]]
    (sle (dot 'weights 'left) (dot 'weights 'right)))
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['weights-positive (vle (vz 'weights) 'weights)]
     ['ordered (vle 'left 'right)]]
    (app (function/const* 'signed/at-most-respects-equivalence [])
         (dot 'left 'weights) (dot 'weights 'left)
         (dot 'right 'weights) (dot 'weights 'right)
         (app (function/const* 'vector/dot-commutative [])
              'left 'weights)
         (app (function/const* 'vector/dot-commutative [])
              'right 'weights)
         (app (function/const* 'vector/dot-left-monotone [])
              'left 'right 'weights 'ordered 'weights-positive)))})

(def dot-nonnegative-spec
  {:name 'vector/dot-nonnegative :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['left-positive (vle (vz 'left) 'left)]
     ['right-positive (vle (vz 'right) 'right)]]
    (sle signed-zero (dot 'left 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['left-positive (vle (vz 'left) 'left)]
     ['right-positive (vle (vz 'right) 'right)]]
    (app (function/const* 'signed/at-most-respects-equivalence [])
         (dot (vz 'left) 'right) signed-zero
         (dot 'left 'right) (dot 'left 'right)
         (app (function/const* 'vector/dot-zero-like-left [])
              'left 'right)
         (app (function/const* 'signed/equivalent-reflexive [])
              (dot 'left 'right))
         (app (function/const* 'vector/dot-left-monotone [])
              (vz 'left) 'left 'right
              'left-positive 'right-positive)))})

(def action-nonnegative-spec
  {:name 'matrix/vector-multiply-nonnegative :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['values-positive (vle (vz 'values) 'values)]]
    (vle (vz (action 'rows 'values)) (action 'rows 'values)))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['values-positive (vle (vz 'values) 'values)]]
    (let [m
          (function/lam
           [['rs matrix-type]]
           (function/forall
            [['rp (mle (mz 'rs) 'rs)]]
            (vle (vz (action 'rs 'values)) (action 'rs 'values))))
          b (function/lam [['rp (mle (mz (nm)) (nm))]] trivial)
          s
          (function/lam
           [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
           (function/lam
            [['rp (mle (mz (cm 'row 'tail)) (cm 'row 'tail))]]
            (let [hr (vle (vz 'row) 'row) tr (mle (mz 'tail) 'tail)]
              (conjp
               (sle signed-zero (dot 'row 'values))
               (vle (vz (action 'tail 'values)) (action 'tail 'values))
               (app (function/const* 'vector/dot-nonnegative [])
                    'row 'values (pl hr tr 'rp) 'values-positive)
               (app 'ih (prop-right hr tr 'rp))))))]
      (app (mr m b s 'rows) 'rows-positive)))})

(def action-monotone-values-spec
  {:name 'matrix/vector-multiply-monotone-values :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['ordered (vle 'left 'right)]]
    (vle (action 'rows 'left) (action 'rows 'right)))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)] ['ordered (vle 'left 'right)]]
    (let [m
          (function/lam
           [['rs matrix-type]]
           (function/forall
            [['rp (mle (mz 'rs) 'rs)]]
            (vle (action 'rs 'left) (action 'rs 'right))))
          b (function/lam [['rp (mle (mz (nm)) (nm))]] trivial)
          s
          (function/lam
           [['row vector-type] ['tail matrix-type] ['ih (app m 'tail)]]
           (function/lam
            [['rp (mle (mz (cm 'row 'tail)) (cm 'row 'tail))]]
            (let [hr (vle (vz 'row) 'row) tr (mle (mz 'tail) 'tail)]
              (conjp
               (sle (dot 'row 'left) (dot 'row 'right))
               (vle (action 'tail 'left) (action 'tail 'right))
               (app (function/const* 'vector/dot-right-monotone [])
                    'row 'left 'right (pl hr tr 'rp) 'ordered)
               (app 'ih (prop-right hr tr 'rp))))))]
      (app (mr m b s 'rows) 'rows-positive)))})

(def action-monotone-rows-spec
  {:name 'matrix/vector-multiply-monotone-rows :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['ordered (mle 'left 'right)]
     ['values-positive (vle (vz 'values) 'values)]]
    (vle (action 'left 'values) (action 'right 'values)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['ordered (mle 'left 'right)]
     ['values-positive (vle (vz 'values) 'values)]]
    (let [om
          (function/lam
           [['l matrix-type]]
           (function/forall
            [['r matrix-type] ['ord (mle 'l 'r)]]
            (vle (action 'l 'values) (action 'r 'values))))
          ob
          (let [e (nm) rm (function/lam [['r matrix-type]]
                                  (function/forall [['ord (mle e 'r)]]
                                                   (vle (action e 'values)
                                                        (action 'r 'values))))]
            (function/lam
             [['r matrix-type]]
             (mr rm
                 (function/lam [['ord (mle e e)]] trivial)
                 (function/lam
                  [['rh vector-type] ['rt matrix-type] ['ignored (app rm 'rt)]]
                  (function/lam [['ord (mle e (cm 'rh 'rt))]]
                                (absurd (vle (action e 'values)
                                             (action (cm 'rh 'rt) 'values))
                                        'ord)))
                 'r)))
          os
          (function/lam
           [['lh vector-type] ['lt matrix-type] ['ih (app om 'lt)]]
           (let [l (cm 'lh 'lt)
                 rm (function/lam [['r matrix-type]]
                      (function/forall [['ord (mle l 'r)]]
                                       (vle (action l 'values)
                                            (action 'r 'values))))]
             (function/lam
              [['r matrix-type]]
              (mr rm
                  (function/lam [['ord (mle l (nm))]]
                                (absurd (vle (action l 'values)
                                             (action (nm) 'values)) 'ord))
                  (function/lam
                   [['rh vector-type] ['rt matrix-type] ['ignored (app rm 'rt)]]
                   (function/lam
                    [['ord (mle l (cm 'rh 'rt))]]
                    (let [ho (vle 'lh 'rh) to (mle 'lt 'rt)]
                      (conjp
                       (sle (dot 'lh 'values) (dot 'rh 'values))
                       (vle (action 'lt 'values) (action 'rt 'values))
                       (app (function/const* 'vector/dot-left-monotone [])
                            'lh 'rh 'values (pl ho to 'ord) 'values-positive)
                       (app 'ih 'rt (prop-right ho to 'ord))))))
                  'r))))]
      (app (mr om ob os 'left) 'right 'ordered)))})

(def action-monotone-spec
  {:name 'matrix/vector-multiply-monotone :universes []
   :type
   (function/forall
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-values vector-type] ['right-values vector-type]
     ['right-rows-positive (mle (mz 'right-rows) 'right-rows)]
     ['values-positive (vle (vz 'left-values) 'left-values)]
     ['rows-ordered (mle 'left-rows 'right-rows)]
     ['values-ordered (vle 'left-values 'right-values)]]
    (vle (action 'left-rows 'left-values)
         (action 'right-rows 'right-values)))
   :value
   (function/lam
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-values vector-type] ['right-values vector-type]
     ['right-rows-positive (mle (mz 'right-rows) 'right-rows)]
     ['values-positive (vle (vz 'left-values) 'left-values)]
     ['rows-ordered (mle 'left-rows 'right-rows)]
     ['values-ordered (vle 'left-values 'right-values)]]
    (app (function/const* 'vector/at-most-transitive [])
         (action 'left-rows 'left-values)
         (action 'right-rows 'left-values)
         (action 'right-rows 'right-values)
         (app (function/const* 'matrix/vector-multiply-monotone-rows [])
              'left-rows 'right-rows 'left-values
              'rows-ordered 'values-positive)
         (app (function/const* 'matrix/vector-multiply-monotone-values [])
              'right-rows 'left-values 'right-values
              'right-rows-positive 'values-ordered)))})

(def definition-specs [])
(def theorem-specs
  [dot-left-monotone-spec dot-right-monotone-spec dot-nonnegative-spec
   action-nonnegative-spec action-monotone-values-spec
   action-monotone-rows-spec action-monotone-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.signed-scale-sign])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'signed/multiply-right-monotone :signed-multiply-monotone multiply-monotone/multiply-right-monotone-spec) (extend-spec-if-missing 'signed/add-monotone :signed-order-monotone order-monotone/add-monotone-spec) (support/extend-with :finite-matrix-positive-action theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.positive-action))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
