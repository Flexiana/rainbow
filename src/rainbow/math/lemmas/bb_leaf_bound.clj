(ns rainbow.math.lemmas.bb-leaf-bound
  "General lemmas: bb leaf bound. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at le below]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.nat.divmod :as divmod]
            [rainbow.math.nat.pair-index-inverse :as pairs]))

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

(defn extend-environment [checked-environment]
  (-> checked-environment
      lp/extend-environment
      divmod/extend-environment
      pairs/extend-environment
      (support/extend-with :expr-sum-bb-leaf-bound theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
