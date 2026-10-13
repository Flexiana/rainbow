(ns rainbow.math.rational.signed.lp-scaling-bound
  "Transport a bound between formal D^2/D-scaled objectives to original sums.
  A positive rational D is cancelled three times, avoiding an assumed positive
  representation of D^3. No endpoint-equivalence premise is assumed. This is
  an objective inequality theorem, not a feasibility or host-code theorem."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.map-sum-scale :as sum-scale]
            [rainbow.math.rational.signed.scale-reflection :as reflection]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nat reflection/nat)
(def signed reflection/signed)
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(defn- list-of [A] (f/app (f/const* 'data/List [data-level]) A))
(defn- coefficient [ap adp] (app 'nnrat/make (app 'data/succ ap) adp))
(defn- cube [c] (ring/rmul (ring/rmul c c) c))
(defn- scale [c x] (app 'signed/scale c x))
(defn- le [x y] (app 'signed/at-most x y))
(defn- pos [x] (app 'signed/positive x))
(defn- neg [x] (app 'signed/negative x))
(defn- nested [c x] (scale c (scale c (scale c x))))
(defn- cube-to-nested [c x]
  (let [triple #(ring/rmul c (ring/rmul c (ring/rmul c %)))]
    (ring/equiv
     (ring/radd (ring/rmul (cube c) (pos x)) (triple (neg x)))
     (ring/radd (triple (pos x)) (ring/rmul (cube c) (neg x))))))

(def scale-positive-cube-reflects-order-spec
  {:name 'signed/scale-positive-cube-reflects-order :universes []
   :type
   (f/forall
    [['ap nat] ['adp nat] ['left signed] ['right signed]
     ['ordered (le (scale (cube (coefficient 'ap 'adp)) 'left)
                   (scale (cube (coefficient 'ap 'adp)) 'right))]]
    (le 'left 'right))
   :value
   (f/lam
    [['ap nat] ['adp nat] ['left signed] ['right signed]
     ['ordered (le (scale (cube (coefficient 'ap 'adp)) 'left)
                   (scale (cube (coefficient 'ap 'adp)) 'right))]]
    (let [c (coefficient 'ap 'adp)
          once-left (scale c 'left) once-right (scale c 'right)
          twice-left (scale c once-left) twice-right (scale c once-right)
          nested-bound
          (app 'signed/at-most-respects-equivalence
               (scale (cube c) 'left) (nested c 'left)
               (scale (cube c) 'right) (nested c 'right)
               (cube-to-nested c 'left) (cube-to-nested c 'right) 'ordered)
          twice-bound
          (app 'signed/scale-positive-reflects-order 'ap 'adp
               twice-left twice-right nested-bound)
          once-bound
          (app 'signed/scale-positive-reflects-order 'ap 'adp
               once-left once-right twice-bound)]
      (app 'signed/scale-positive-reflects-order 'ap 'adp 'left 'right once-bound)))})

(defn- objective [A coefficients values indices]
  (poly 'signed/map-sum A
        (f/lam [['i A]]
               (app 'signed/multiply (f/app coefficients 'i) (f/app values 'i)))
        indices))
(defn- scaled-objective [A d coefficients values indices]
  (poly 'signed/map-sum A
        (f/lam [['i A]]
               (app 'signed/multiply
                    (scale (ring/rmul d d) (f/app coefficients 'i))
                    (scale d (f/app values 'i))))
        indices))

(def lp-scaled-objectives-bound-spec
  (let [d (coefficient 'ap 'adp)
        left (objective 'A 'margins 'plan 'columns)
        right (objective 'A 'capacities 'prices 'rows)
        checked-left (scaled-objective 'A d 'margins 'plan 'columns)
        checked-right (scaled-objective 'A d 'capacities 'prices 'rows)
        bindings [['A type-u] ['ap nat] ['adp nat]
                  ['margins (f/arrow 'A signed)] ['plan (f/arrow 'A signed)]
                  ['capacities (f/arrow 'A signed)] ['prices (f/arrow 'A signed)]
                  ['columns (list-of 'A)] ['rows (list-of 'A)]
                  ['scaled-bound (le checked-left checked-right)]]]
    {:name 'signed/lp-scaled-objectives-bound :universes ['u]
     :type (f/forall bindings (le left right))
     :value
     (f/lam
      bindings
      (app 'signed/scale-positive-cube-reflects-order 'ap 'adp left right
           (app 'signed/at-most-respects-equivalence
                checked-left (scale (cube d) left)
                checked-right (scale (cube d) right)
                (poly 'signed/lp-objective-cubic-scale 'A d 'margins 'plan 'columns)
                (poly 'signed/lp-objective-cubic-scale 'A d 'capacities 'prices 'rows)
                'scaled-bound)))}))

(def definition-specs [])
(def theorem-specs [scale-positive-cube-reflects-order-spec lp-scaled-objectives-bound-spec])
(defn extend-environment [env]
  (-> env
      reflection/extend-environment
      sum-scale/extend-environment
      (support/extend-with :signed-lp-scaling-bound theorem-specs)))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
