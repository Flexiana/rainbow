(ns rainbow.math.rational.signed.lp-equality-row
  "Formal equality-row expansion into two signed inequality rows.
  Generic in the carrier, coefficient/value maps and finite index list. This
  proves the mathematical row relation, not host array append or free-price split."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.lp-objective-negate :as sense]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed sense/signed)
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(defn- neg [x] (app 'signed/negate x))
(defn- eqv [x y] (app 'signed/equivalent x y))
(defn- le [x y] (app 'signed/at-most x y))
(defn- both [P Q] (app 'proposition/conjunction P Q))
(defn- objective [A c x xs]
  (poly 'signed/map-sum A
        (f/lam [['i A]] (app 'signed/multiply (f/app c 'i) (f/app x 'i))) xs))
(def bindings
  [['A type-u] ['a (f/arrow 'A signed)] ['x (f/arrow 'A signed)]
   ['xs (f/app (f/const* 'data/List [data-level]) 'A)] ['b signed]])
(def original (objective 'A 'a 'x 'xs))
(def negated (objective 'A (f/lam [['i 'A]] (neg (f/app 'a 'i))) 'x 'xs))
(def equality-row (eqv original 'b))
(def upper-row (le original 'b))
(def lower-row (le negated (neg 'b)))
(def expanded-rows (both upper-row lower-row))

(def equality-row-expand-spec
  {:name 'signed/lp-equality-row-expand :universes ['u]
   :type (f/forall (conj bindings ['same equality-row]) expanded-rows)
   :value
   (f/lam
    (conj bindings ['same equality-row])
    (app 'proposition/conjoin upper-row lower-row
         (app 'signed/equivalent-to-at-most original 'b 'same)
         (app 'signed/equivalent-to-at-most negated (neg 'b)
              (app 'signed/equivalent-transitive negated (neg original) (neg 'b)
                   (poly 'signed/lp-objective-negate 'A 'a 'x 'xs)
                   (app 'signed/negate-respects-equivalence original 'b 'same)))))})

(def equality-row-contract-spec
  {:name 'signed/lp-equality-row-contract :universes ['u]
   :type (f/forall (conj bindings ['rows expanded-rows]) equality-row)
   :value
   (f/lam
    (conj bindings ['rows expanded-rows])
    (app 'signed/at-most-antisymmetric original 'b
         (app 'proposition/left upper-row lower-row 'rows)
         (poly 'signed/lp-negated-objective-bound-to-lower 'A 'a 'x 'xs 'b
               (app 'proposition/right upper-row lower-row 'rows))))})

(def equality-row-expansion-equivalence-spec
  {:name 'signed/lp-equality-row-expansion-equivalence :universes ['u]
   :type (f/forall bindings (app 'proposition/equivalence equality-row expanded-rows))
   :value
   (f/lam bindings
          (app 'proposition/equivalence-intro equality-row expanded-rows
               (poly 'signed/lp-equality-row-expand 'A 'a 'x 'xs 'b)
               (poly 'signed/lp-equality-row-contract 'A 'a 'x 'xs 'b)))})

(def theorem-specs [equality-row-expand-spec equality-row-contract-spec
                    equality-row-expansion-equivalence-spec])
;; Reuse just the existing antisymmetry resident, not the limit capstone.
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-objective-negate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/add-spec-shared :signed-limit-uniqueness uniqueness/signed-at-most-antisymmetric-spec) (support/extend-with :signed-lp-equality-row theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-equality-row))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
