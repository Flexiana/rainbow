(ns rainbow.math.quantifier
  "Surface proof-data constructors for nested quantifier families."
  (:require [clojure.walk :as walk]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]))

(defn nested-forall [bindings body]
  (function/forall bindings body))

(defn nested-existence [level bindings body]
  (if-let [[name carrier] (first bindings)]
    (proposition/existence
     level carrier
     (function/lam [[name carrier]]
                   (nested-existence level (next bindings) body)))
    body))

(defn introduce-existences
  "Builds nested existential evidence. `bindings` name each predicate binder;
  `values` are the witnesses inserted for those binders."
  [level bindings values body evidence]
  (if-let [[name carrier] (first bindings)]
    (let [predicate
          (function/lam
           [[name carrier]]
           (nested-existence level (next bindings) body))
          replacement (first values)
          substituted-body (walk/postwalk-replace {name replacement} body)
          substituted-evidence
          (walk/postwalk-replace {name replacement} evidence)]
      (function/app
       (function/const* 'proposition/witness [level])
       carrier predicate replacement
       (introduce-existences level (next bindings) (next values)
                             substituted-body substituted-evidence)))
    evidence))

(defn eliminate-existences
  "Eliminates nested existential evidence into proposition `result`.
  `continuation` receives the innermost evidence surface form."
  [level bindings body evidence result continuation]
  (letfn [(step [remaining current depth]
            (if-let [[name carrier] (first remaining)]
              (let [predicate
                    (function/lam
                     [[name carrier]]
                     (nested-existence level (next remaining) body))
                    inner-evidence (symbol (str "nested-evidence-" depth))]
                (function/app
                 (function/const* 'proposition/use-witness [level])
                 carrier predicate result current
                 (function/lam
                  [[name carrier]
                   [inner-evidence (function/app predicate name)]]
                  (step (next remaining) inner-evidence (inc depth)))))
              (continuation current)))]
    (step bindings evidence 0)))
