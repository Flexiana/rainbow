(ns rainbow.math.rational.signed.add-associative
  "Associativity of signed-rational addition up to Grothendieck equivalence.

    (a + b) + c  ~  a + (b + c)

  The unfolded signed equivalence is an equality, up to nnrat equivalence, of
  two six-summand cross sums.  The verified nnrat ring normalizer constructs the
  proof from existing additive laws; the kernel checks the resulting term and
  the module introduces no axioms."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))

(def add-associative-spec
  {:name 'signed/add-associative :universes []
   :type
   (function/forall
    [['a signed] ['b signed] ['c signed]]
    (equivalent (add (add 'a 'b) 'c)
                (add 'a (add 'b 'c))))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]]
    (let [pa (positive 'a) na (negative 'a)
          pb (positive 'b) nb (negative 'b)
          pc (positive 'c) nc (negative 'c)
          left-positive (ring/radd (ring/radd pa pb) pc)
          left-negative (ring/radd (ring/radd na nb) nc)
          right-positive (ring/radd pa (ring/radd pb pc))
          right-negative (ring/radd na (ring/radd nb nc))]
      (ring/equiv
       (ring/radd left-positive right-negative)
       (ring/radd right-positive left-negative))))})

(def definition-specs [])
(def theorem-specs [add-associative-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.ring])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-add-associative theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.add-associative))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
