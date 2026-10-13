(ns rainbow.algorithms.proofs.ahof.lbfgs
  "AHoF O30 L-BFGS: limited-memory BFGS storing recent (s, y) pairs; the stored gradient\n  change is y = g_{k+1} - g_k: gradient-change g-new g-old = g-new - g-old. Worked: 3-1=2.
  Values proved by signed cross-product equivalence. Proved native and axiom-free.
  Requires signed/subtract, signed/from-nnrat, signed/equivalent (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.lbfgs`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
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
(defn- signed-op [l r] (function/app (function/const* 'signed/subtract []) l r))
(defn- signed-equivalent [l r] (function/app (function/const* 'signed/equivalent []) l r))
(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- op [a b] (function/app (function/const* 'lbfgs/gradient-change []) a b))

(def op-spec
  {:name 'lbfgs/gradient-change :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam [['a signed] ['b signed]] (signed-op 'a 'b))})

(def change-example-spec
  {:name 'lbfgs/change-example :kind :definition :universes [] :type signed
   :value (op (signed-of 3) (signed-of 1))})

(def no-change-spec
  {:name 'lbfgs/no-change :kind :definition :universes [] :type signed
   :value (op (signed-of 2) (signed-of 2))})

(def definition-specs [op-spec change-example-spec no-change-spec])

(def op-unfold-spec
  {:name 'lbfgs/gradient-change-unfold :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (equality signed (op 'a 'b) (signed-op 'a 'b)))
   :value (function/lam [['a signed] ['b signed]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      signed (op 'a 'b)))})

(def change-example-is-2-spec
  {:name 'lbfgs/change-example-is-2 :universes []
   :type (signed-equivalent (function/const* 'lbfgs/change-example []) (signed-of 2))
   :value (signed-equivalent-cross (function/const* 'lbfgs/change-example []) (signed-of 2))})

(def no-change-is-0-spec
  {:name 'lbfgs/no-change-is-0 :universes []
   :type (signed-equivalent (function/const* 'lbfgs/no-change []) (signed-of 0))
   :value (signed-equivalent-cross (function/const* 'lbfgs/no-change []) (signed-of 0))})

(def theorem-specs [op-unfold-spec change-example-is-2-spec no-change-is-0-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-lbfgs
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
