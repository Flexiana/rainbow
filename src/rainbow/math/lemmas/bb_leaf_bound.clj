(ns rainbow.math.lemmas.bb-leaf-bound
  "General lemmas: bb leaf bound. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at le below]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.nat.divmod :as divmod]
            [rainbow.math.nat.pair-index-inverse :as pairs]
            [rainbow.module :as module]))

(defn nadd [a b] (call 'algebra/nat-add a b))

(defn nmul [a b] (call 'nat/multiply a b))

(defn eq-nat [a b] (f/app (f/const* 'equality/Eq [[:succ [:zero]]]) nat a b))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [[:succ [:zero]]]) nat x y h P px))

(def rectangular-spec
  (s/spec 'nat/pair-index-below-rectangular
          [['n nat] ['a nat] ['b nat] ['L nat] ['ha (below 'a 'n)] ['hb (below 'b 'L)]]
          (below (nadd 'a (nmul 'b 'n)) (nmul 'L 'n))
          (call 'nat/at-most-transitive (nadd (s/succ 'a) (nmul 'b 'n)) (nmul (s/succ 'b) 'n) (nmul 'L 'n)
                (call 'nat/add-right-monotone (nmul 'b 'n) (s/succ 'a) 'n 'ha)
                (call 'nat/multiply-right-monotone 'n (s/succ 'b) 'L 'hb))))

(def theorem-specs [rectangular-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.lemmas.lp-duality rainbow.math.nat.infinite rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.nnrat.identities rainbow.math.rational.signed.limit-uniqueness rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.nat.divmod rainbow.math.nat.pair-index-inverse rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.unit-laws rainbow.math.checks rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :expr-sum-bb-leaf-bound theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.bb-leaf-bound))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
