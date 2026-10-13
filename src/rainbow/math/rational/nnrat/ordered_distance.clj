(ns rainbow.math.rational.nnrat.ordered-distance
  "Exact reconstruction from ordered nonnegative-rational distance.

  Natural distance reconstructs an ordered upper endpoint:

      left <= right  ->  left + distance(left,right) = right.

  The natural proof extracts the additive witness already carried by `nat/at-most`
  and removes a common translation with `nat/distance-add-left`.  The NNRAT
  theorem lifts that equality through the quotient-safe cross-product
  representation.  This provides an executable, canonical remainder rather than
  an existentially chosen gap.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.rational.nnrat.distance :as distance]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- nmul [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- ndistance [left right]
  (app (function/const* 'nat/distance []) left right))
(defn- nat-at-most [left right]
  (app (function/const* 'nat/at-most []) left right))
(defn- eq-nat [left right]
  (function/equality type-level nat left right))
(defn- eq-refl [value]
  (app (function/const* 'equality/reflexive [type-level]) nat value))
(defn- eq-sym [left right same]
  (app (function/const* 'equality/symmetric [type-level])
       nat left right same))
(defn- eq-trans [left middle right first second]
  (app (function/const* 'equality/transitive [type-level])
       nat left middle right first second))
(defn- eq-congruent [mapping left right same]
  (app (function/const* 'equality/congruent-function
                        [type-level type-level])
       nat nat mapping left right same))
(defn- ring-eq [left right]
  (:proof (ring/prove-nat-eq left right)))

(defn- rnum [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- dpre [value]
  (app (function/const* 'nnrat/denominator-predecessor []) value))
(defn- den [value]
  (app (function/const* 'nnrat/denominator []) value))
(defn- nsucc [value]
  (app (function/const* 'data/succ []) value))
(defn- combine [left right]
  (app (function/const* 'nnrat/combine-denominator-predecessors [])
       left right))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rat-distance [left right]
  (app (function/const* 'nnrat/distance []) left right))
(defn- rat-at-most [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))

(def nat-add-distance-of-at-most-spec
  (let [motive
        (fn [left right]
          (function/lam
           [['gap nat]]
           (eq-nat (nadd left 'gap) right)))]
    {:name 'nat/add-distance-of-at-most
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]
       ['ordered (nat-at-most 'left 'right)]]
      (eq-nat (nadd 'left (ndistance 'left 'right)) 'right))
     :value
     (function/lam
      [['left nat] ['right nat]
       ['ordered (nat-at-most 'left 'right)]]
      (let [goal (eq-nat (nadd 'left (ndistance 'left 'right)) 'right)]
        (app
         (function/const* 'proposition/use-witness [type-level])
         nat (motive 'left 'right) goal 'ordered
         (function/lam
          [['gap nat]
           ['same (eq-nat (nadd 'left 'gap) 'right)]]
          (let [original-distance (ndistance 'left 'right)
                witnessed-distance (ndistance 'left (nadd 'left 'gap))
                padded-distance
                (ndistance (nadd 'left nat-zero) (nadd 'left 'gap))
                zero-distance (ndistance nat-zero 'gap)
                substitute-right
                (eq-sym
                 witnessed-distance original-distance
                 (eq-congruent
                  (function/lam
                   [['value nat]] (ndistance 'left 'value))
                  (nadd 'left 'gap) 'right 'same))
                pad-left
                (eq-congruent
                 (function/lam
                  [['value nat]] (ndistance 'value (nadd 'left 'gap)))
                 'left (nadd 'left nat-zero)
                 (eq-sym
                  (nadd 'left nat-zero) 'left
                  (app (function/const* 'algebra/nat-add-zero-right [])
                       'left)))
                remove-translation
                (app (function/const* 'nat/distance-add-left [])
                     'left nat-zero 'gap)
                distance-is-gap
                (eq-trans
                 original-distance witnessed-distance 'gap
                 substitute-right
                 (eq-trans
                  witnessed-distance padded-distance 'gap
                  pad-left
                  (eq-trans padded-distance zero-distance 'gap
                            remove-translation
                            (eq-refl 'gap))))
                add-gap
                (eq-congruent
                 (function/lam [['value nat]] (nadd 'left 'value))
                 original-distance 'gap distance-is-gap)]
            (eq-trans
             (nadd 'left original-distance)
             (nadd 'left 'gap) 'right add-gap 'same))))))}))

(def nnrat-add-distance-of-at-most-spec
  {:name 'nnrat/add-distance-of-at-most
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['ordered (rat-at-most 'left 'right)]]
    (req (radd 'left (rat-distance 'left 'right)) 'right))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['ordered (rat-at-most 'left 'right)]]
    (let [nx (rnum 'left)
          ny (rnum 'right)
          dpx (dpre 'left)
          dpy (dpre 'right)
          dx (den 'left)
          dy (den 'right)
          left-cross (nmul nx dy)
          right-cross (nmul ny dx)
          delta (ndistance left-cross right-cross)
          distance-den (nsucc (combine dpx dpy))
          shared-den (nmul dx dy)
          sum-den (nsucc (combine dpx (combine dpx dpy)))
          start
          (nmul (nadd (nmul nx distance-den) (nmul delta dx)) dy)
          left-replaced
          (nmul (nadd (nmul nx shared-den) (nmul delta dx)) dy)
          common-left (nmul shared-den (nadd left-cross delta))
          common-right (nmul shared-den right-cross)
          right-first (nmul ny (nmul dx distance-den))
          right-second (nmul ny (nmul dx shared-den))
          finish (nmul ny sum-den)
          distance-den-law
          (app (function/const* 'nnrat/denominator-combine []) dpx dpy)
          sum-den-law
          (app (function/const* 'nnrat/denominator-combine [])
               dpx (combine dpx dpy))
          reconstruct-cross
          (app (function/const* 'nat/add-distance-of-at-most [])
               left-cross right-cross
               (app (function/const* 'nnrat/at-most-to-cross [])
                    'left 'right 'ordered))
          left-path
          (eq-trans
           start left-replaced common-left
           (eq-congruent
            (function/lam
             [['value nat]]
             (nmul (nadd (nmul nx 'value) (nmul delta dx)) dy))
            distance-den shared-den distance-den-law)
           (ring-eq left-replaced common-left))
          center
          (eq-congruent
           (function/lam [['value nat]] (nmul shared-den 'value))
           (nadd left-cross delta) right-cross reconstruct-cross)
          right-path
          (eq-trans
           finish right-first common-right
           (eq-congruent
            (function/lam [['value nat]] (nmul ny 'value))
            sum-den (nmul dx distance-den) sum-den-law)
           (eq-trans
            right-first right-second common-right
            (eq-congruent
             (function/lam
              [['value nat]] (nmul ny (nmul dx 'value)))
             distance-den shared-den distance-den-law)
            (ring-eq right-second common-right)))]
      (eq-trans
       start common-right finish
       (eq-trans start common-left common-right left-path center)
       (eq-sym finish common-right right-path))))})

(def definition-specs [])
(def theorem-specs
  [nat-add-distance-of-at-most-spec
   nnrat-add-distance-of-at-most-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.distance])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :nnrat-ordered-distance theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.ordered-distance))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
