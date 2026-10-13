(ns rainbow.math.logic.function
  "Clojure-data constructors for reusable higher-order function predicates."
  (:require [rainbow.math.logic.proposition :as proposition]))

(defn forall [bindings body] [:forall (vec bindings) body])
(defn lam [bindings body] [:fn (vec bindings) body])
(defn arrow [& values] (into [:->] values))
(defn app [function & arguments] (into [:app function] arguments))
(defn const* [alias levels] [:const alias (vec levels)])

(defn equality [level carrier left right]
  (app (const* 'equality/Eq [level]) carrier left right))

(defn involutive [level carrier function]
  (forall [['value carrier]]
          (equality level carrier
                    (app function (app function 'value))
                    'value)))

(defn injective [domain-level codomain-level domain codomain function]
  (forall [['left domain] ['right domain]
           ['same-image
            (equality codomain-level codomain
                      (app function 'left) (app function 'right))]]
          (equality domain-level domain 'left 'right)))

(defn surjective [domain-level codomain-level domain codomain function]
  (forall [['target codomain]]
          (proposition/existence
           domain-level domain
           (lam [['source domain]]
                (equality codomain-level codomain
                          (app function 'source) 'target)))))

(defn bijective [domain-level codomain-level domain codomain function]
  (proposition/conjunction
   (injective domain-level codomain-level domain codomain function)
   (surjective domain-level codomain-level domain codomain function)))

(defn injective2
  [left-level right-level codomain-level left right codomain function]
  (forall [['left-a left] ['left-b left]
           ['right-a right] ['right-b right]
           ['same-image
            (equality codomain-level codomain
                      (app function 'left-a 'right-a)
                      (app function 'left-b 'right-b))]]
          (proposition/conjunction
           (equality left-level left 'left-a 'left-b)
           (equality right-level right 'right-a 'right-b))))
