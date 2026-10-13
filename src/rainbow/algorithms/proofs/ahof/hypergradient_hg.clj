(ns rainbow.algorithms.proofs.ahof.hypergradient-hg
  "AHoF O25 Hypergradient Descent: adapt the learning rate online by a hypergradient\n  correction, updating rate-update rate adjustment = rate + adjustment. Worked: 1+2=3.
  Values proved by signed cross-product equivalence. Proved native and axiom-free.
  Requires signed/add, signed/from-nnrat, signed/equivalent (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.hypergradient-hg`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole-nnrat [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- signed-of [n] (function/app (function/const* 'signed/from-nnrat []) (whole-nnrat n)))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- signed-positive [v] (function/app (function/const* 'signed/positive []) v))
(defn- signed-negative [v] (function/app (function/const* 'signed/negative []) v))
(defn- signed-op [l r] (function/app (function/const* 'signed/add []) l r))
(defn- signed-equivalent [l r] (function/app (function/const* 'signed/equivalent []) l r))
(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- op [a b] (function/app (function/const* 'hypergrad-ng/rate-update []) a b))

(def op-spec
  {:name 'hypergrad-ng/rate-update :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam [['a signed] ['b signed]] (signed-op 'a 'b))})

(def update-example-spec
  {:name 'hypergrad-ng/update-example :kind :definition :universes [] :type signed
   :value (op (signed-of 1) (signed-of 2))})

(def no-adjustment-spec
  {:name 'hypergrad-ng/no-adjustment :kind :definition :universes [] :type signed
   :value (op (signed-of 3) (signed-of 0))})

(def definition-specs [op-spec update-example-spec no-adjustment-spec])

(def op-unfold-spec
  {:name 'hypergrad-ng/rate-update-unfold :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (equality signed (op 'a 'b) (signed-op 'a 'b)))
   :value (function/lam [['a signed] ['b signed]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      signed (op 'a 'b)))})

(def update-example-is-3-spec
  {:name 'hypergrad-ng/update-example-is-3 :universes []
   :type (signed-equivalent (function/const* 'hypergrad-ng/update-example []) (signed-of 3))
   :value (signed-equivalent-cross (function/const* 'hypergrad-ng/update-example []) (signed-of 3))})

(def no-adjustment-is-3-spec
  {:name 'hypergrad-ng/no-adjustment-is-3 :universes []
   :type (signed-equivalent (function/const* 'hypergrad-ng/no-adjustment []) (signed-of 3))
   :value (signed-equivalent-cross (function/const* 'hypergrad-ng/no-adjustment []) (signed-of 3))})

(def theorem-specs [op-unfold-spec update-example-is-3-spec no-adjustment-is-3-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-hypergradient-hg (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.hypergradient-hg))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
