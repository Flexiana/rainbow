(ns rainbow.math.nat.at-most-add
  "Three one-line order facts about addition that the program-family index arithmetic keeps needing
  (nat/at-most a b unfolds to exists e, a + e = b; addition recurses on its LEFT argument, so
  `a <= a + b` is a direct witness but `a <= b + a` needs commutativity and the nested form needs
  associativity):
     nat/at-most-add-right  : a <= a + b
     nat/at-most-add-left   : a <= b + a
     nat/at-most-add-nested : a + b <= a + (b + c)
     nat/add-left-swap         : x + (d + y) = d + (x + y)      (assoc, comm, assoc)
     nat/at-most-add-left-swap : x + (d + y) <= d + (x + y)    (the same, as an order fact)
  The swap pair is what lets a depth d threaded on the LEFT of every family index commute past a
  fixed layout offset when bounding reads under extra bindings."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(defn- app [f & args] (apply function/app f args))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- refl-nat [x] (app (function/const* 'equality/reflexive [type-level]) nat x))
(defn- witness [P w pf] (app (function/const* 'proposition/witness [type-level]) nat P w pf))
(defn- esym-nat [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- etr-nat [a b c h1 h2] (app (function/const* 'equality/transitive [type-level]) nat a b c h1 h2))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- add-assoc [a b c] (app (function/const* 'nat/add-associative []) a b c))
(defn- add-comm [a b] (app (function/const* 'nat/add-commutative []) a b))

(def at-most-add-right-spec
  {:name 'nat/at-most-add-right :universes []
   :type (function/forall [['a nat] ['b nat]] (at-most 'a (nadd 'a 'b)))
   :value (function/lam [['a nat] ['b nat]]
                        (witness (function/lam [['e nat]] (eq-nat (nadd 'a 'e) (nadd 'a 'b))) 'b (refl-nat (nadd 'a 'b))))})

(def at-most-add-left-spec
  {:name 'nat/at-most-add-left :universes []
   :type (function/forall [['a nat] ['b nat]] (at-most 'a (nadd 'b 'a)))
   :value (function/lam [['a nat] ['b nat]]
                        (witness (function/lam [['e nat]] (eq-nat (nadd 'a 'e) (nadd 'b 'a))) 'b
                                 (app (function/const* 'nat/add-commutative []) 'a 'b)))})

(def at-most-add-nested-spec
  {:name 'nat/at-most-add-nested :universes []
   :type (function/forall [['a nat] ['b nat] ['c nat]] (at-most (nadd 'a 'b) (nadd 'a (nadd 'b 'c))))
   :value (function/lam [['a nat] ['b nat] ['c nat]]
                        (witness (function/lam [['e nat]] (eq-nat (nadd (nadd 'a 'b) 'e) (nadd 'a (nadd 'b 'c)))) 'c
                                 (app (function/const* 'nat/add-associative []) 'a 'b 'c)))})

(def add-left-swap-spec
  {:name 'nat/add-left-swap :universes []
   :type (function/forall [['x nat] ['d nat] ['y nat]] (eq-nat (nadd 'x (nadd 'd 'y)) (nadd 'd (nadd 'x 'y))))
   :value (function/lam
           [['x nat] ['d nat] ['y nat]]
           (etr-nat (nadd 'x (nadd 'd 'y)) (nadd (nadd 'x 'd) 'y) (nadd 'd (nadd 'x 'y))
                    (esym-nat (nadd (nadd 'x 'd) 'y) (nadd 'x (nadd 'd 'y)) (add-assoc 'x 'd 'y))
                    (etr-nat (nadd (nadd 'x 'd) 'y) (nadd (nadd 'd 'x) 'y) (nadd 'd (nadd 'x 'y))
                             (subst-nat (nadd 'x 'd) (nadd 'd 'x) (add-comm 'x 'd)
                                        (function/lam [['t nat]] (eq-nat (nadd (nadd 'x 'd) 'y) (nadd 't 'y)))
                                        (refl-nat (nadd (nadd 'x 'd) 'y)))
                             (add-assoc 'd 'x 'y))))})

(def at-most-add-left-swap-spec
  {:name 'nat/at-most-add-left-swap :universes []
   :type (function/forall [['x nat] ['d nat] ['y nat]] (at-most (nadd 'x (nadd 'd 'y)) (nadd 'd (nadd 'x 'y))))
   :value (function/lam
           [['x nat] ['d nat] ['y nat]]
           (subst-nat (nadd 'x (nadd 'd 'y)) (nadd 'd (nadd 'x 'y)) (app (function/const* 'nat/add-left-swap []) 'x 'd 'y)
                      (function/lam [['t nat]] (at-most (nadd 'x (nadd 'd 'y)) 't))
                      (app (function/const* 'nat/at-most-reflexive []) (nadd 'x (nadd 'd 'y)))))})

(def theorem-specs [at-most-add-right-spec at-most-add-left-spec at-most-add-nested-spec
                    add-left-swap-spec at-most-add-left-swap-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nat-at-most-add theorem-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
