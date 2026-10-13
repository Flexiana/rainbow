(ns rainbow.math.rational.signed.scale-reflection
  "Positive rational scaling reflects signed order. Together with explicit
  endpoint equivalences this transports a checked scaled bound to its original
  values. It does not assert that a host-language transformation produces those
  equivalences. Positivity is structural: make (succ ap) adp, never zero."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.nnrat.order-scale :as order-scale]
            [rainbow.math.rational.signed.scale-order :as scale-order]
            [rainbow.math.rational.signed.order-respects :as respects]))

(def nat (f/const* 'data/Nat []))
(def signed scale-order/signed)
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- coefficient [ap adp] (app 'nnrat/make (app 'data/succ ap) adp))
(defn- scale [c x] (app 'signed/scale c x))
(defn- le [x y] (app 'signed/at-most x y))
(defn- eqv [x y] (app 'signed/equivalent x y))
(defn- pos [x] (app 'signed/positive x))
(defn- neg [x] (app 'signed/negative x))

(def scale-positive-reflects-order-spec
  {:name 'signed/scale-positive-reflects-order :universes []
   :type
   (f/forall [['ap nat] ['adp nat] ['left signed] ['right signed]
              ['ordered (le (scale (coefficient 'ap 'adp) 'left)
                            (scale (coefficient 'ap 'adp) 'right))]]
             (le 'left 'right))
   :value
   (f/lam
    [['ap nat] ['adp nat] ['left signed] ['right signed]
     ['ordered (le (scale (coefficient 'ap 'adp) 'left)
                   (scale (coefficient 'ap 'adp) 'right))]]
    (let [c (coefficient 'ap 'adp)
          l (ring/radd (pos 'left) (neg 'right))
          r (ring/radd (pos 'right) (neg 'left))
          cl (ring/rmul c l)
          cr (ring/rmul c r)
          expanded-l (ring/radd (ring/rmul c (pos 'left))
                               (ring/rmul c (neg 'right)))
          expanded-r (ring/radd (ring/rmul c (pos 'right))
                               (ring/rmul c (neg 'left)))]
      (app 'nnrat/at-most-multiply-left-cancel 'ap 'adp l r
           (app 'nnrat/at-most-respects-equivalence
                cl expanded-l cr expanded-r
                (ring/equiv cl expanded-l) (ring/equiv cr expanded-r)
                'ordered))))})

(def scaled-bound-to-original-spec
  {:name 'signed/scaled-bound-to-original :universes []
   :type
   (f/forall
    [['ap nat] ['adp nat] ['left signed] ['right signed]
     ['checked-left signed] ['checked-right signed]
     ['left-same (eqv 'checked-left (scale (coefficient 'ap 'adp) 'left))]
     ['right-same (eqv 'checked-right (scale (coefficient 'ap 'adp) 'right))]
     ['checked-bound (le 'checked-left 'checked-right)]]
    (le 'left 'right))
   :value
   (f/lam
    [['ap nat] ['adp nat] ['left signed] ['right signed]
     ['checked-left signed] ['checked-right signed]
     ['left-same (eqv 'checked-left (scale (coefficient 'ap 'adp) 'left))]
     ['right-same (eqv 'checked-right (scale (coefficient 'ap 'adp) 'right))]
     ['checked-bound (le 'checked-left 'checked-right)]]
    (app 'signed/scale-positive-reflects-order 'ap 'adp 'left 'right
         (app 'signed/at-most-respects-equivalence
              'checked-left (scale (coefficient 'ap 'adp) 'left)
              'checked-right (scale (coefficient 'ap 'adp) 'right)
              'left-same 'right-same 'checked-bound)))})

(def definition-specs [])
(def theorem-specs [scale-positive-reflects-order-spec scaled-bound-to-original-spec])
(defn extend-environment [env]
  (-> env
      scale-order/extend-environment
      order-scale/extend-environment
      respects/extend-environment
      (support/extend-with :signed-scale-reflection theorem-specs)))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
