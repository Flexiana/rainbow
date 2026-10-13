(ns rainbow.math.rational.nnrat.farkas-vector-step
  "The unified representation, the recursion step:
  one closed elimination step in the held next-variable representation, and
  its instantiation of the over-variable recursion skeleton.

  farkas-vector-round eliminates a variable and yields a feasible AFFINE
  system; farkas-vector-unit-column-lower/-upper re-present that affine system
  as a HELD next-variable system (constant carried as a unit column). Composed
  -- unpacking the round's existential in between -- they give one step in a
  single representation:

    nnrat/farkas-vector-step : given lower/upper next-variable constraints held
      at x1 (tail head x2), there EXIST lower/upper next-variable constraints
      held at x2 (tail head the unit value).

  The stated output has the same held representation. Its existential lists
  are not related to the input lists by this type; empty lists can witness it.
  Wrapping the value into a closed predicate Feasible : Nat -> Prop
  (nnrat/farkas-vector-feasible k = EXISTS value and lower/upper next-variable
  lists held at that value over the unit column) makes this exactly the step
  the recursion skeleton folds:

    nnrat/farkas-vector-eliminate : Feasible n -> Feasible 0, via
      nnrat/farkas-eliminate-all with step = farkas-vector-step.

  This instantiates a recursion schema, but Feasible ignores k; the types of
  farkas-vector-feasible-step and farkas-vector-eliminate admit identity proofs.
  The theorem does not
  establish elimination of n coordinates from a specified input system.
  Symbolic survivor columns, a source-related transformation, its existential
  projection theorem, and separate multiplier/dual-extraction proofs remain
  required. The new source-row reconstruction results do not silently change
  this predicate or its consumers. Native proof data, axiom-free. See
  the design notes."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-vector-round :as vr]
            [rainbow.math.rational.nnrat.farkas-vector-unit-column :as vuc]
            [rainbow.math.rational.nnrat.farkas-eliminate-all :as elim]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def lp (function/app (function/const* 'data/List [type-level]) pair-nn))

;; next-variable constraint list, affine row list, and the two pair types
(def n-ar (product nnrat lp))
(def n-br (product nnrat n-ar))
(def nvc (product nnrat n-br))
(def list-nvc (function/app (function/const* 'data/List [type-level]) nvc))
(def p2 (product nnrat nnrat))
(def arow (product nnrat p2))
(def list-a (function/app (function/const* 'data/List [type-level]) arow))
(def aff-pair (product list-a list-a))         ; round's existential carrier
(def nvc-pair (product list-nvc list-nvc))     ; step's existential carrier

(def one (function/const* 'nnrat/one []))
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- pair2 [a b x y]
  (function/app (function/const* 'data/pair [type-level type-level]) a b x y))

(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))

(defn- lowers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied []) rows w))
(defn- uppers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied []) rows w))
(defn- lowers-hold [cs x] (function/app (function/const* 'nnrat/farkas-cross-vectors-lowers-hold []) cs x))
(defn- uppers-hold [cs x] (function/app (function/const* 'nnrat/farkas-cross-vectors-uppers-hold []) cs x))
(defn- map-uppers [lst x] (function/app (function/const* 'nnrat/farkas-adapter-map-uppers []) lst x))
(defn- repr [rows] (function/app (function/const* 'nnrat/farkas-vector-unit-repr []) rows))

(defn- vector-round [lowers uppers x1 x2 lh uh]
  (function/app (function/const* 'nnrat/farkas-vector-round []) lowers uppers x1 x2 lh uh))
(defn- unit-lower [rows x2 h]
  (function/app (function/const* 'nnrat/farkas-vector-unit-column-lower []) rows x2 h))
(defn- unit-upper [rows x2 h]
  (function/app (function/const* 'nnrat/farkas-vector-unit-column-upper []) rows x2 h))

;; existence machinery
(defn- exists [T pred] (function/app (function/const* 'proposition/existence [type-level]) T pred))
(defn- witness [T pred value ev]
  (function/app (function/const* 'proposition/witness [type-level]) T pred value ev))
(defn- use-witness [T pred result ev cont]
  (function/app (function/const* 'proposition/use-witness [type-level]) T pred result ev cont))

;; the round's existential goal (matches nnrat_farkas_partition_list's goal)
(defn- aff-goal-pred [w]
  (function/lam
   [['pr aff-pair]]
   (conjunction (lowers-sat (fst list-a list-a 'pr) w)
                (uppers-sat (snd list-a list-a 'pr) w))))

;; the step's held existential goal at value x, tail head the unit value
(defn- held-goal-pred [x]
  (function/lam
   [['pr nvc-pair]]
   (conjunction (lowers-hold (map-uppers (fst list-nvc list-nvc 'pr) one) x)
                (uppers-hold (map-uppers (snd list-nvc list-nvc 'pr) one) x))))
(defn- held-goal [x] (exists nvc-pair (held-goal-pred x)))

(def step-spec
  {:name 'nnrat/farkas-vector-step
   :universes []
   :type
   (function/forall
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['lh (lowers-hold (map-uppers 'lowers 'x2) 'x1)]
     ['uh (uppers-hold (map-uppers 'uppers 'x2) 'x1)]]
    (held-goal 'x2))
   :value
   (function/lam
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['lh (lowers-hold (map-uppers 'lowers 'x2) 'x1)]
     ['uh (uppers-hold (map-uppers 'uppers 'x2) 'x1)]]
    (let [round-out (vector-round 'lowers 'uppers 'x1 'x2 'lh 'uh)]
      (use-witness
       aff-pair (aff-goal-pred 'x2) (held-goal 'x2) round-out
       (function/lam
        [['pr aff-pair]
         ['pp (function/app (aff-goal-pred 'x2) 'pr)]]
        (let [l-aff (fst list-a list-a 'pr)
              u-aff (snd list-a list-a 'pr)
              lsat (left-conjunct (lowers-sat l-aff 'x2) (uppers-sat u-aff 'x2) 'pp)
              usat (right-conjunct (lowers-sat l-aff 'x2) (uppers-sat u-aff 'x2) 'pp)
              held-lo (unit-lower l-aff 'x2 lsat)
              held-up (unit-upper u-aff 'x2 usat)
              new-pr (pair2 list-nvc list-nvc (repr l-aff) (repr u-aff))]
          (witness nvc-pair (held-goal-pred 'x2) new-pr
                   (conjoin (lowers-hold (map-uppers (repr l-aff) one) 'x2)
                            (uppers-hold (map-uppers (repr u-aff) one) 'x2)
                            held-lo held-up)))))))})

;; the closed feasibility predicate: EXISTS value and held next-variable lists
(def feasible-spec
  {:name 'nnrat/farkas-vector-feasible
   :kind :definition
   :universes []
   :type (function/arrow nat 'Prop)
   :value
   (function/lam
    [['k nat]]
    (exists nnrat
            (function/lam
             [['x nnrat]] (held-goal 'x))))})

(def definition-specs [feasible-spec])

(defn- feasible [k] (function/app (function/const* 'nnrat/farkas-vector-feasible []) k))
(defn- succ [k] (function/app (function/const* 'data/succ []) k))

;; step wrapped to Feasible(succ k) -> Feasible k, uniform in k
(def feasible-step-spec
  {:name 'nnrat/farkas-vector-feasible-step
   :universes []
   :type
   (function/forall
    [['k nat] ['fk (feasible (succ 'k))]]
    (feasible 'k))
   :value
   (function/lam
    [['k nat] ['fk (feasible (succ 'k))]]
    ;; unpack (x, pr, holds) from Feasible(succ k); apply farkas-vector-step
    ;; at value x, tail head one; re-pack as Feasible k at value one.
    (use-witness
     nnrat (function/lam [['x nnrat]] (held-goal 'x)) (feasible 'k) 'fk
     (function/lam
      [['x nnrat] ['hx (held-goal 'x)]]
      (use-witness
       nvc-pair (held-goal-pred 'x) (feasible 'k) 'hx
       (function/lam
        [['pr nvc-pair]
         ['pp (function/app (held-goal-pred 'x) 'pr)]]
        (let [lowers (fst list-nvc list-nvc 'pr)
              uppers (snd list-nvc list-nvc 'pr)
              lh (left-conjunct (lowers-hold (map-uppers lowers one) 'x)
                                (uppers-hold (map-uppers uppers one) 'x) 'pp)
              uh (right-conjunct (lowers-hold (map-uppers lowers one) 'x)
                                 (uppers-hold (map-uppers uppers one) 'x) 'pp)
              ;; farkas-vector-step with x1=x, x2=one
              stepped (function/app (function/const* 'nnrat/farkas-vector-step [])
                                    lowers uppers 'x one lh uh)]
          ;; stepped : held-goal one; re-pack as Feasible k (witness value one)
          (witness nnrat (function/lam [['x nnrat]] (held-goal 'x)) one stepped)))))))})

;; instantiate the recursion skeleton
(def eliminate-spec
  {:name 'nnrat/farkas-vector-eliminate
   :universes []
   :type
   (function/forall
    [['n nat] ['init (feasible 'n)]]
    (feasible nat-zero))
   :value
   (function/lam
    [['n nat] ['init (feasible 'n)]]
    (function/app
     (function/app
      (function/app
       (function/app
        (function/const* 'nnrat/farkas-eliminate-all [])
        (function/const* 'nnrat/farkas-vector-feasible []))
       (function/const* 'nnrat/farkas-vector-feasible-step []))
      'n)
     'init))})

(def theorem-specs [step-spec feasible-step-spec eliminate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-vector-round rainbow.math.rational.nnrat.farkas-vector-unit-column rainbow.math.rational.nnrat.farkas-eliminate-all])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-vector-step (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-vector-step))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
