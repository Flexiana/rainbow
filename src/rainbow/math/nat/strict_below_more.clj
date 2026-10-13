(ns rainbow.math.nat.strict-below-more
  "Small reusable nat lemmas for indexed-fold attainment (pure nat, off the trusted base):
     nat/add-successor-right     : i + succ e = succ (i + e)   (add recurses left, so this needs proof)
     nat/strict-below-self       : m < succ m
     nat/strict-below-weaken     : i < m -> i < succ m"
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.strict-below-split :as split]))

(def ^:private ulvl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(def ^:private nat-zero (function/const* 'data/zero []))
(defn- add [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- eqn [x y] (app (function/const* 'equality/Eq [ulvl]) nat x y))
(defn- refl [x] (app (function/const* 'equality/reflexive [ulvl]) nat x))
(defn- symm [a b h] (app (function/const* 'equality/symmetric [ulvl]) nat a b h))
(defn- trans [a b c h1 h2] (app (function/const* 'equality/transitive [ulvl]) nat a b c h1 h2))
(defn- subst [x y h P px] (app (function/const* 'equality/substitution [ulvl]) nat x y h P px))
(defn- add-comm [a b] (app (function/const* 'nat/add-commutative []) a b))
(defn- strict-below [v u] (app (function/const* 'nat/strict-below []) v u))
(defn- witness [pred value evidence]
  (app (function/const* 'proposition/witness [ulvl]) nat pred value evidence))
(defn- succ-cong [x y h] (subst x y h (function/lam [['t nat]] (eqn (succ x) (succ 't))) (refl (succ x))))

;; i + succ e = succ (i + e). add i (succ e) ~ add (succ e) i = succ(add e i) ~ succ(add i e).
(def add-successor-right-spec
  {:name 'nat/add-successor-right
   :universes []
   :type (function/forall [['i nat] ['e nat]] (eqn (add 'i (succ 'e)) (succ (add 'i 'e))))
   :value (function/lam
           [['i nat] ['e nat]]
           (trans (add 'i (succ 'e)) (succ (add 'e 'i)) (succ (add 'i 'e))
                  (add-comm 'i (succ 'e))                       ; add i (succ e) = add (succ e) i = succ(add e i)
                  (succ-cong (add 'e 'i) (add 'i 'e) (add-comm 'e 'i))))})

(defn- add-succ-right [i e] (app (function/const* 'nat/add-successor-right []) i e))

;; m < succ m : witness 0, since (succ m) + 0 = succ m (add-commutative strips the +0).
(def strict-below-self-spec
  {:name 'nat/strict-below-self
   :universes []
   :type (function/forall [['m nat]] (strict-below 'm (succ 'm)))
   :value (function/lam
           [['m nat]]
           (witness (function/lam [['e nat]] (eqn (add (succ 'm) 'e) (succ 'm)))
                    nat-zero
                    (add-comm (succ 'm) nat-zero)))})

;; i < m -> i < succ m : from witness e (succ i + e = m), use witness (succ e).
(def strict-below-weaken-spec
  {:name 'nat/strict-below-weaken
   :universes []
   :type (function/forall [['i nat] ['m nat] ['h (strict-below 'i 'm)]]
                          (strict-below 'i (succ 'm)))
   :value (function/lam
           [['i nat] ['m nat] ['h (strict-below 'i 'm)]]
           (app 'h (strict-below 'i (succ 'm))
                (function/lam
                 [['e nat] ['pf (eqn (add (succ 'i) 'e) 'm)]]
                 (witness (function/lam [['e-prime nat]] (eqn (add (succ 'i) 'e-prime) (succ 'm)))
                          (succ 'e)
                          ;; eqn (add (succ i)(succ e)) (succ m):
                          ;; add(succ i)(succ e) =defeq= succ(add i (succ e)) ; add-succ-right -> succ(succ(add i e))
                          ;; =defeq= succ(add(succ i) e) ; succ-cong pf -> succ m
                          (trans (add (succ 'i) (succ 'e)) (succ (succ (add 'i 'e))) (succ 'm)
                                 (succ-cong (add 'i (succ 'e)) (succ (add 'i 'e)) (add-succ-right 'i 'e))
                                 (succ-cong (add (succ 'i) 'e) 'm 'pf))))))})

(def theorem-specs [add-successor-right-spec strict-below-self-spec strict-below-weaken-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.strict-below-split])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nat-strict-below-more theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.strict-below-more))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
