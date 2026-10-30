(ns rainbow.math.rational.signed.lp-pointwise-bridge
  "LP scaling-bridge proof producer built from a pointwise correspondence.

  It replaces the aggregate fold (`mapsum-corresponds` in
  or/lp_certificate.clj) with a pointwise construction that avoids exposing the
  aggregate fold's repeated reductions to the kernel:

    table-product-correspondence : a data/Nat.rec proof, for EVERY index, that the
      actual scaled/original product tables correspond (following nat-lookup's
      semantics -- index 0 is the head, successor recurses, the last entry repeats).
      Each concrete leaf is kernel-checked via lp/computed-equivalence; no assumed
      correspondence, no host-arithmetic equality.
    signed/map-sum-respects-equivalence lifts that all-index proof to each aggregate,
      feeding the existing signed order transport and signed/lp-scaled-objectives-bound
      to reconstruct the original instance's bound-spec type.

  IMPORTANT: this module only READS or/lp_certificate.clj (the LP proof producer /
  reserved 5c file) via private-var refs -- it does NOT modify it, and is NOT wired into
  lp/bound. The actual scaled/original tables are kept as inputs (no idealized
  substitution). API/report/universal wiring stays out of scope. Axiom-free on the
  validated 2-column fixtures (see the gate test); tampered tables are kernel-rejected."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.lp-scaling-bound :as scaling]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private N (f/const* 'data/Nat []))
(defn- app [nm & args] (apply f/app (f/const* nm []) args))
(defn- equiv [x y] (app 'signed/equivalent x y))
(defn- sum [mapping indices]
  (f/app (f/const* 'signed/map-sum [[:zero]]) N mapping indices))
(defn- scaled-value [d v] (app 'signed/scale d v))
(defn- multiply [x y] (app 'signed/multiply x y))

(defn product-maps
  "The actual (scaled) and formally-scaled (original) product maps, built from the
  literal tables via lp/nat-lookup -- the same endpoints the runtime bridge uses."
  [sl sr ol oright d]
  (let [lookup (fn [values] (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal values)))
        slf (lookup sl) srf (lookup sr) olf (lookup ol) orf (lookup oright)
        dd (app 'nnrat/multiply d d)]
    [(f/lam [['j N]] (multiply (f/app slf 'j) (f/app srf 'j)))
     (f/lam [['j N]] (multiply (scaled-value dd (f/app olf 'j))
                               (scaled-value d (f/app orf 'j))))]))

(defn table-product-correspondence
  "Proof for EVERY Nat index of the concrete tables, including their repeated final
  entry. Nat.rec follows the actual lookup semantics; leaf arithmetic is still
  kernel-checked (lp/computed-equivalence), not accepted on host equality or an
  assumed premise."
  [sl sr ol oright d]
  (assert (and (seq sl) (apply = (map count [sl sr ol oright]))))
  (let [[left right] (product-maps sl sr ol oright d)
        at (fn [i] (equiv (f/app left i) (f/app right i)))
        leaf (fn [i] (#'lp/computed-equivalence (f/app left i) (f/app right i)))]
    (if (= 1 (count sl))
      (f/lam [['index N]] (leaf 'index))
      (let [tail-proof (table-product-correspondence
                        (subvec sl 1) (subvec sr 1) (subvec ol 1) (subvec oright 1) d)]
        (f/lam
         [['index N]]
         (f/app (f/const* 'data/Nat.rec [[:zero]])
                (f/lam [['k N]] (at 'k))
                (leaf (#'lp/numeral 0))
                (f/lam [['predecessor N] ['ignored (at 'predecessor)]]
                       (f/app tail-proof 'predecessor))
                'index))))))

(defn pointwise-bridge-spec
  "Reconstruct an instance's original-unit bound-spec {:type :value} using the
  pointwise producer in place of the two aggregate folds. Endpoints/target
  unchanged from lp/bound-spec; only the correspondence proof construction differs."
  [instance]
  (let [[scaled D] (lp/integerize instance)
        original (#'lp/standard-form instance)
        checked (#'lp/standard-form scaled)
        ot (#'lp/instance-terms original)
        st (#'lp/instance-terms checked)
        d (#'lp/coefficient-of D) dd (app 'nnrat/multiply d d)
        fobj (f/lam [['j N]] (multiply (f/app (:c st) 'j) (f/app (:x st) 'j)))
        gobj (f/lam [['j N]] (multiply (scaled-value dd (f/app (:c ot) 'j))
                                       (scaled-value d (f/app (:x ot) 'j))))
        fdual (f/lam [['i N]] (multiply (f/app (:b st) 'i) (f/app (:y st) 'i)))
        gdual (f/lam [['i N]] (multiply (scaled-value dd (f/app (:b ot) 'i))
                                        (scaled-value d (f/app (:y ot) 'i))))
        obj-pointwise (table-product-correspondence
                       (:margins checked) (:plan checked) (:margins original) (:plan original) d)
        dual-pointwise (table-product-correspondence
                        (:capacities checked) (:prices checked)
                        (:capacities original) (:prices original) d)
        congruence (fn [a b evidence indices]
                     (f/app (f/const* 'signed/map-sum-respects-equivalence [[:zero]])
                            N a b evidence indices))
        obj-eq (congruence fobj gobj obj-pointwise (:cols ot))
        dual-eq (congruence fdual gdual dual-pointwise (:rows ot))
        new-premise (app 'signed/at-most-respects-equivalence
                         (sum fobj (:cols ot)) (sum gobj (:cols ot))
                         (sum fdual (:rows ot)) (sum gdual (:rows ot))
                         obj-eq dual-eq (:value (lp/bound-spec 'pointwise/scaled-bound checked)))]
    {:type (:type (lp/bound-spec 'pointwise/original-bound original))
     :value (f/app (f/const* 'signed/lp-scaled-objectives-bound [[:zero]])
                   N (#'lp/numeral (dec D)) (#'lp/numeral 0)
                   (:c ot) (:x ot) (:b ot) (:y ot) (:cols ot) (:rows ot) new-premise)}))

(defn objective-sum-correspondence-spec
  "The objective aggregate correspondence for an instance: map-sum congruence over the
  per-index pointwise proof. Unlike the full bridge, this needs no weak-duality premise,
  so it validates the producer on ARBITRARY (incl. nonuniform) tables -- the Nat.rec
  recursion exercises a distinct leaf per column."
  [instance]
  (let [[scaled D] (lp/integerize instance)
        original (#'lp/standard-form instance)
        checked (#'lp/standard-form scaled)
        ot (#'lp/instance-terms original)
        st (#'lp/instance-terms checked)
        d (#'lp/coefficient-of D) dd (app 'nnrat/multiply d d)
        fobj (f/lam [['j N]] (multiply (f/app (:c st) 'j) (f/app (:x st) 'j)))
        gobj (f/lam [['j N]] (multiply (scaled-value dd (f/app (:c ot) 'j))
                                       (scaled-value d (f/app (:x ot) 'j))))
        obj-pointwise (table-product-correspondence
                       (:margins checked) (:plan checked) (:margins original) (:plan original) d)
        obj-eq (f/app (f/const* 'signed/map-sum-respects-equivalence [[:zero]])
                      N fobj gobj obj-pointwise (:cols ot))]
    {:type (equiv (sum fobj (:cols ot)) (sum gobj (:cols ot)))
     :value obj-eq}))

(defn tampered-objective-table
  "Alter the first scaled margin for a correspondence control. When its plan
  component is nonzero the product changes and the claim must be type-rejected.
  When that component is zero, the unchanged product legitimately still checks;
  this helper is not an unconditional negative test for arbitrary instances."
  [instance]
  (let [[scaled D] (lp/integerize instance)
        original (#'lp/standard-form instance)
        checked (#'lp/standard-form scaled)
        d (#'lp/coefficient-of D)
        tampered-margins (update (:margins checked) 0 inc)
        [left right] (product-maps tampered-margins (:plan checked)
                                   (:margins original) (:plan original) d)]
    {:type (f/forall [['index N]] (equiv (f/app left 'index) (f/app right 'index)))
     :value (table-product-correspondence
             tampered-margins (:plan checked) (:margins original) (:plan original) d)}))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-duality-on rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.lp-scaling-bound])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  checked-environment)

(defn extend-environment
  "Chain the dependency environments the producer's output is checked against.
  Registers no instance-specific declarations -- the producer is validated in the
  gate test. or/lp_certificate.clj is required read-only and left unchanged." [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.lp-pointwise-bridge))
