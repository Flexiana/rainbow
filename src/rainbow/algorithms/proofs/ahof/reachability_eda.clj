(ns rainbow.algorithms.proofs.ahof.reachability-eda
  "Final Kochenderfer straggler cores (reachability, robustness envelope, adaptive SA,
  estimation-of-distribution program search) as higher-order-function compositions,
  proved axiom-free, extending the 222 AHoF catalog:

    V10.3  backward reachability     : a state is back-reachable if SOME successor is (OR)
    V9.3   conservative linearization : reachable-set upper envelope = center + radius
    O8.7   adaptive simulated annealing: accept-if-better keeps the lower cost (min)
    O23.10 probabilistic grammar EDA  : move the grammar toward elite (convex update)
    O23.14 PIPE prototype tree EDA    : move the prototype toward elite (convex update)

  Includes a small boolean-OR (dual of rainbow.math.logic.boolean-and) for reachability.
  Native and axiom-free; chains nnrat-convex (-> wsum2, minmax) on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.convex :as convex]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def rone (function/const* 'nnrat/one []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- wsum2 [w0 w1 v0 v1] (function/app (function/const* 'nnrat/wsum2 []) w0 w1 v0 v1))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rmin [a b] (function/app (function/const* 'minmax/min []) a b))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- reflexive-bool [v]
  (function/app (function/const* 'equality/reflexive [type-level]) bool v))
(def ^:private nat (function/const* 'data/Nat []))
(defn- num [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- den [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- equiv-cross [x lit]
  (function/app (function/const* 'equality/reflexive [type-level]) nat (nmul (num x) (den lit))))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(defn- numeral [n] (nth (iterate succ zero-nat) n))
(defn- rational [n d-pred] (function/app (function/const* 'nnrat/make []) (numeral n) (numeral d-pred)))
(def half (rational 1 1))

;; ---- boolean OR (dual of boolean-and): or a b = if a then true else b --------
(def or-spec
  {:name 'boolean/or :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam [['a bool] ['b bool]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      bool (eq-bool 'a 'a) 'a true-value 'b))})

;; a reachable predecessor makes the OR true (intro-left, reduction)
(def or-true-left-spec
  {:name 'boolean/or-true-left :universes []
   :type (function/forall [['b bool]]
                          (eq-bool (function/app (function/const* 'boolean/or []) true-value 'b) true-value))
   :value (function/lam [['b bool]] (reflexive-bool true-value))})

;; ---- V10.3 backward reachability --------------------------------------------
(def backward-reachable-spec
  {:name 'reach/backward-reachable :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam [['succ0 bool] ['succ1 bool]]
                        (function/app (function/const* 'boolean/or []) 'succ0 'succ1))})

(def backward-reach-from-successor-spec
  {:name 'reach/backward-reach-from-successor :universes []
   :type (function/forall [['succ1 bool]]
                          (eq-bool (function/app (function/const* 'reach/backward-reachable []) true-value 'succ1)
                                   true-value))
   :value (function/lam [['succ1 bool]]
                        (function/app (function/const* 'boolean/or-true-left []) 'succ1))})

;; ---- V9.3 conservative linearization: reachable upper envelope ---------------
(def conservative-upper-spec
  {:name 'reach/conservative-upper :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['center nnrat] ['radius nnrat]] (radd 'center 'radius))})

;; worked: center 1, radius 1/2 -> conservative upper bound 3/2
(def conservative-upper-example-spec
  {:name 'reach/conservative-upper-example :universes []
   :type (equiv (function/app (function/const* 'reach/conservative-upper []) rone half) (rational 3 1))
   :value (equiv-cross (function/app (function/const* 'reach/conservative-upper []) rone half) (rational 3 1))})

;; ---- O8.7 adaptive simulated annealing: accept-if-better (min cost) ----------
(def asa-accept-spec
  {:name 'opt/asa-accept :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['current nnrat] ['candidate nnrat]] (rmin 'current 'candidate))})

(def asa-accept-not-worse-spec
  {:name 'opt/asa-accept-not-worse :universes []
   :type (function/forall [['current nnrat] ['candidate nnrat]]
                          (at-most (function/app (function/const* 'opt/asa-accept []) 'current 'candidate) 'current))
   :value (function/lam [['current nnrat] ['candidate nnrat]]
                        (function/app (function/const* 'minmax/min-lower-left []) 'current 'candidate))})

;; ---- O23.10 probabilistic grammar EDA: convex move toward elite --------------
(def grammar-update-spec
  {:name 'eda/grammar-update :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['old nnrat] ['elite nnrat]]
                        (wsum2 'w0 'w1 'old 'elite))})

(def grammar-update-within-max-spec
  {:name 'eda/grammar-update-within-max :universes []
   :type (function/forall [['w0 nnrat] ['w1 nnrat] ['old nnrat] ['elite nnrat]
                           ['hw (equiv (radd 'w0 'w1) rone)]]
                          (at-most (function/app (function/const* 'eda/grammar-update []) 'w0 'w1 'old 'elite)
                                   (rmax 'old 'elite)))
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['old nnrat] ['elite nnrat]
                         ['hw (equiv (radd 'w0 'w1) rone)]]
                        (function/app (function/const* 'nnrat/convex-at-most-max [])
                                      'w0 'w1 'old 'elite 'hw))})

;; ---- O23.14 PIPE prototype tree EDA: convex move toward elite ----------------
(def pipe-update-spec
  {:name 'eda/pipe-update :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['old nnrat] ['elite nnrat]]
                        (wsum2 'w0 'w1 'old 'elite))})

(def pipe-update-within-max-spec
  {:name 'eda/pipe-update-within-max :universes []
   :type (function/forall [['w0 nnrat] ['w1 nnrat] ['old nnrat] ['elite nnrat]
                           ['hw (equiv (radd 'w0 'w1) rone)]]
                          (at-most (function/app (function/const* 'eda/pipe-update []) 'w0 'w1 'old 'elite)
                                   (rmax 'old 'elite)))
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['old nnrat] ['elite nnrat]
                         ['hw (equiv (radd 'w0 'w1) rone)]]
                        (function/app (function/const* 'nnrat/convex-at-most-max [])
                                      'w0 'w1 'old 'elite 'hw))})

(def definition-specs
  [or-spec backward-reachable-spec conservative-upper-spec asa-accept-spec
   grammar-update-spec pipe-update-spec])
(def theorem-specs
  [or-true-left-spec backward-reach-from-successor-spec conservative-upper-example-spec
   asa-accept-not-worse-spec grammar-update-within-max-spec pipe-update-within-max-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.convex])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-reachability-eda (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.reachability-eda))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
