(ns rainbow.math.rational.signed.lp-scaling-feasibility
  "Forward feasibility scaling and universal-bound transport on listed indices.
  Forward preservation holds for every nonnegative rational D; universal-bound
  transport uses positive D and the proved original-objective bound theorem.
  No converse feasibility or candidate-bijection hypothesis is required."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.lp-scaling-bound :as bounds]
            [rainbow.math.rational.signed.pointwise-order :as pointwise]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed bounds/signed)
(def nat bounds/nat)
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(def sz (f/const* 'signed/zero []))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(defn- list-of [A] (f/app (f/const* 'data/List [data-level]) A))
(defn- mapping [A] (f/arrow A signed))
(defn- scale [d x] (app 'signed/scale d x))
(defn- square [d] (app 'nnrat/multiply d d))
(defn- le [x y] (app 'signed/at-most x y))
(defn- all-le [A left right xs] (poly 'signed/all-at-most A left right xs))
(defn- zero-on [A] (f/lam [['ignored A]] sz))
(defn- scaled-map [A d xs] (f/lam [['i A]] (scale d (f/app xs 'i))))
(defn- scaled-matrix [A B d M]
  (f/lam [['i A] ['j B]] (scale d (f/app (f/app M 'i) 'j))))
(defn- objective [A c x indices]
  (poly 'signed/map-sum A
        (f/lam [['j A]] (app 'signed/multiply (f/app c 'j) (f/app x 'j))) indices))
(defn- activity [A B M x cols]
  (f/lam [['i A]] (objective B (f/app M 'i) x cols)))
(defn- sym [x y h]
  (app 'nnrat/equivalent-symmetric
       (app 'nnrat/add (app 'signed/positive x) (app 'signed/negative y))
       (app 'nnrat/add (app 'signed/positive y) (app 'signed/negative x)) h))

;; Unary implication is the existing binary combiner with its source duplicated.
;; The second premise adds no assumption; both copies are the same evidence.
(defn- map-order [A left right new-left new-right xs step evidence]
  (poly 'signed/all-at-most-combine A left right left right new-left new-right xs
        (f/lam [['i A] ['first (le (f/app left 'i) (f/app right 'i))]
                ['second (le (f/app left 'i) (f/app right 'i))]]
               (f/app step 'i 'first))
        evidence evidence))

(def scaling-preserves-nonnegative-on-spec
  (let [z (zero-on 'A) sx (scaled-map 'A 'd 'x)
        bindings [['A type-u] ['d nnrat] ['x (mapping 'A)] ['cols (list-of 'A)]
                  ['nonnegative (all-le 'A z 'x 'cols)]]]
    {:name 'signed/scaling-preserves-nonnegative-on :universes ['u]
     :type (f/forall bindings (all-le 'A z sx 'cols))
     :value
     (f/lam
      bindings
      (map-order
       'A z 'x z sx 'cols
       (f/lam
        [['i 'A] ['ordered (le sz (f/app 'x 'i))]]
        (let [scaled-value (scale 'd (f/app 'x 'i))]
          (app 'signed/at-most-respects-equivalence
               (scale 'd sz) sz scaled-value scaled-value
               (app 'signed/scale-zero 'd)
               (app 'signed/equivalent-reflexive scaled-value)
               (app 'signed/scale-monotone 'd sz (f/app 'x 'i) 'ordered))))
       'nonnegative))}))

(def lp-scaling-preserves-primal-feasibility-spec
  (let [Mtype (f/arrow 'A (mapping 'B))
        original (activity 'A 'B 'M 'x 'cols)
        sx (scaled-map 'B 'd 'x)
        scaled (activity 'A 'B (scaled-matrix 'A 'B 'd 'M) sx 'cols)
        sb (scaled-map 'A (square 'd) 'b)
        bindings [['A type-u] ['B type-u] ['d nnrat] ['M Mtype]
                  ['b (mapping 'A)] ['x (mapping 'B)]
                  ['rows (list-of 'A)] ['cols (list-of 'B)]
                  ['feasible (all-le 'A original 'b 'rows)]]]
    {:name 'signed/lp-scaling-preserves-primal-feasibility :universes ['u]
     :type (f/forall bindings (all-le 'A scaled sb 'rows))
     :value
     (f/lam
      bindings
      (map-order
       'A original 'b scaled sb 'rows
       (f/lam
        [['i 'A] ['ordered (le (f/app original 'i) (f/app 'b 'i))]]
        (let [row (f/app 'M 'i)
              original-value (objective 'B row 'x 'cols)
              scaled-value (f/app scaled 'i)
              target (scale (square 'd) (f/app 'b 'i))
              homogeneous (scale (square 'd) original-value)]
          (app 'signed/at-most-respects-equivalence
               homogeneous scaled-value target target
               (sym scaled-value homogeneous
                    (poly 'signed/map-sum-biscaled-products 'B 'd 'd row 'x 'cols))
               (app 'signed/equivalent-reflexive target)
               (app 'signed/scale-monotone (square 'd) original-value (f/app 'b 'i)
                    'ordered))))
       'feasible))}))

(defn- universal-bound [A M b c y rows cols]
  (f/forall
   [['candidate (mapping A)]
    ['feasible (all-le A (activity A A M 'candidate cols) b rows)]
    ['nonnegative (all-le A (zero-on A) 'candidate cols)]]
   (le (objective A c 'candidate cols) (objective A b y rows))))

(def lp-scaled-universal-bound-to-original-spec
  (let [d (app 'nnrat/make (app 'data/succ 'ap) 'adp)
        sM (scaled-matrix 'A 'A d 'M)
        sb (scaled-map 'A (square d) 'b)
        sc (scaled-map 'A (square d) 'c)
        sy (scaled-map 'A d 'y)
        bindings [['A type-u] ['ap nat] ['adp nat]
                  ['M (f/arrow 'A (mapping 'A))] ['b (mapping 'A)]
                  ['c (mapping 'A)] ['y (mapping 'A)]
                  ['rows (list-of 'A)] ['cols (list-of 'A)]
                  ['scaled-universal (universal-bound 'A sM sb sc sy 'rows 'cols)]]
        candidate-bindings
        [['candidate (mapping 'A)]
         ['feasible (all-le 'A (activity 'A 'A 'M 'candidate 'cols) 'b 'rows)]
         ['nonnegative (all-le 'A (zero-on 'A) 'candidate 'cols)]]]
    {:name 'signed/lp-scaled-universal-bound-to-original :universes ['u]
     :type (f/forall bindings (universal-bound 'A 'M 'b 'c 'y 'rows 'cols))
     :value
     (f/lam
      (into bindings candidate-bindings)
      (poly 'signed/lp-scaled-objectives-bound 'A 'ap 'adp
            'c 'candidate 'b 'y 'cols 'rows
            (f/app
             'scaled-universal (scaled-map 'A d 'candidate)
             (poly 'signed/lp-scaling-preserves-primal-feasibility
                   'A 'A d 'M 'b 'candidate 'rows 'cols 'feasible)
             (poly 'signed/scaling-preserves-nonnegative-on
                   'A d 'candidate 'cols 'nonnegative))))}))

(def definition-specs [])
(def theorem-specs [scaling-preserves-nonnegative-on-spec
                    lp-scaling-preserves-primal-feasibility-spec
                    lp-scaled-universal-bound-to-original-spec])
(defn extend-environment [env]
  (-> env bounds/extend-environment pointwise/extend-environment
      (support/extend-with :signed-lp-scaling-feasibility theorem-specs)))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
