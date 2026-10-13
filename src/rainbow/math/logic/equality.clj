(ns rainbow.math.logic.equality
  "Leibniz equality and its initial axiom-free theorem family."
  (:require [rainbow.history.first-tactic-program :as first-tactic-program]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.term :as term]))

(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def sort-u [:sort U])
(def sort-v [:sort V])
(def sort-w [:sort W])

(defn forall [bindings body] [:forall (vec bindings) body])
(defn lam [bindings body] [:fn (vec bindings) body])
(defn arrow [& values] (into [:->] values))
(defn app [function & arguments] (into [:app function] arguments))
(defn const* [alias levels] [:const alias (vec levels)])
(defn eq [a x y] (app (const* 'equality/Eq [U]) a x y))

(def equality-definition
  {:name 'equality/Eq
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type (forall [['A sort-u] ['x 'A] ['y 'A]] 'Prop)
   :value (lam [['A sort-u] ['x 'A] ['y 'A]]
               (forall [['P (arrow 'A 'Prop)]
                        ['px (app 'P 'x)]]
                       (app 'P 'y)))})

(def theorem-specs
  [{:name 'equality/reflexive
    :universes ['u]
    :type (forall [['A sort-u] ['x 'A]] (eq 'A 'x 'x))
    :value (lam [['A sort-u] ['x 'A]
                 ['P (arrow 'A 'Prop)] ['px (app 'P 'x)]]
                'px)}

   {:name 'equality/substitution
    :universes ['u]
    :type (forall [['A sort-u] ['x 'A] ['y 'A]
                   ['h (eq 'A 'x 'y)]
                   ['P (arrow 'A 'Prop)]
                   ['px (app 'P 'x)]]
                  (app 'P 'y))
    :value (lam [['A sort-u] ['x 'A] ['y 'A]
                 ['h (eq 'A 'x 'y)]
                 ['P (arrow 'A 'Prop)]
                 ['px (app 'P 'x)]]
                (app 'h 'P 'px))}

   {:name 'equality/symmetric
    :universes ['u]
    :type (forall [['A sort-u] ['x 'A] ['y 'A] ['h (eq 'A 'x 'y)]]
                  (eq 'A 'y 'x))
    :value (lam [['A sort-u] ['x 'A] ['y 'A] ['h (eq 'A 'x 'y)]]
                (app 'h
                     (lam [['z 'A]] (eq 'A 'z 'x))
                     (app (const* 'equality/reflexive [U]) 'A 'x)))}

   {:name 'equality/transitive
    :universes ['u]
    :type (forall [['A sort-u] ['x 'A] ['y 'A] ['z 'A]
                   ['hxy (eq 'A 'x 'y)] ['hyz (eq 'A 'y 'z)]]
                  (eq 'A 'x 'z))
    :value (lam [['A sort-u] ['x 'A] ['y 'A] ['z 'A]
                 ['hxy (eq 'A 'x 'y)] ['hyz (eq 'A 'y 'z)]
                 ['P (arrow 'A 'Prop)] ['px (app 'P 'x)]]
                (app 'hyz 'P (app 'hxy 'P 'px)))}

   {:name 'equality/congruent-function
    :universes ['u 'v]
    :type (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
                   ['x 'A] ['y 'A] ['h (eq 'A 'x 'y)]]
                  (app (const* 'equality/Eq [V]) 'B (app 'f 'x) (app 'f 'y)))
    :value (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
                 ['x 'A] ['y 'A] ['h (eq 'A 'x 'y)]
                 ['P (arrow 'B 'Prop)] ['pfx (app 'P (app 'f 'x))]]
                (app 'h
                     (lam [['z 'A]] (app 'P (app 'f 'z)))
                     'pfx))}

   {:name 'equality/congruent-argument
    :universes ['u 'v]
    :type (forall [['A sort-u] ['B sort-v]
                   ['f (arrow 'A 'B)] ['g (arrow 'A 'B)]
                   ['h (app (const* 'equality/Eq [[:imax U V]])
                            (arrow 'A 'B) 'f 'g)]
                   ['x 'A]]
                  (app (const* 'equality/Eq [V]) 'B (app 'f 'x) (app 'g 'x)))
    :value (lam [['A sort-u] ['B sort-v]
                 ['f (arrow 'A 'B)] ['g (arrow 'A 'B)]
                 ['h (app (const* 'equality/Eq [[:imax U V]])
                          (arrow 'A 'B) 'f 'g)]
                 ['x 'A]
                 ['P (arrow 'B 'Prop)] ['pfx (app 'P (app 'f 'x))]]
                (app 'h
                     (lam [['k (arrow 'A 'B)]] (app 'P (app 'k 'x)))
                     'pfx))}

   {:name 'equality/proposition-forward
    :universes []
    :type (forall [['A 'Prop] ['B 'Prop]
                   ['h (app (const* 'equality/Eq [[:succ [:zero]]]) 'Prop 'A 'B)]
                   ['a 'A]]
                  'B)
    :value (lam [['A 'Prop] ['B 'Prop]
                 ['h (app (const* 'equality/Eq [[:succ [:zero]]]) 'Prop 'A 'B)]
                 ['a 'A]]
                (app 'h (lam [['P 'Prop]] 'P) 'a))}

   {:name 'equality/proposition-backward
    :universes []
    :type (forall [['A 'Prop] ['B 'Prop]
                   ['h (app (const* 'equality/Eq [[:succ [:zero]]]) 'Prop 'A 'B)]
                   ['b 'B]]
                  'A)
    :value (lam [['A 'Prop] ['B 'Prop]
                 ['h (app (const* 'equality/Eq [[:succ [:zero]]]) 'Prop 'A 'B)]
                 ['b 'B]]
                (app (app 'h
                          (lam [['P 'Prop]] (arrow 'P 'A))
                          (lam [['a 'A]] 'a))
                     'b))}

   {:name 'equality/composed-congruence
    :universes ['u 'v 'w]
    :type (forall [['A sort-u] ['B sort-v] ['C sort-w]
                   ['f (arrow 'A 'B)] ['g (arrow 'B 'C)]
                   ['x 'A] ['y 'A] ['h (eq 'A 'x 'y)]]
                  (app (const* 'equality/Eq [W]) 'C
                       (app 'g (app 'f 'x)) (app 'g (app 'f 'y))))
    :value (lam [['A sort-u] ['B sort-v] ['C sort-w]
                 ['f (arrow 'A 'B)] ['g (arrow 'B 'C)]
                 ['x 'A] ['y 'A] ['h (eq 'A 'x 'y)]
                 ['P (arrow 'C 'Prop)] ['p (app 'P (app 'g (app 'f 'x)))]]
                (app 'h
                     (lam [['z 'A]] (app 'P (app 'g (app 'f 'z))))
                     'p))}

   {:name 'equality/reverse-substitution
    :universes ['u]
    :type (forall [['A sort-u] ['x 'A] ['y 'A]
                   ['h (eq 'A 'x 'y)] ['P (arrow 'A 'Prop)]
                   ['py (app 'P 'y)]]
                  (app 'P 'x))
    :value (lam [['A sort-u] ['x 'A] ['y 'A]
                 ['h (eq 'A 'x 'y)] ['P (arrow 'A 'Prop)]
                 ['py (app 'P 'y)]]
                (app (app 'h
                          (lam [['z 'A]] (arrow (app 'P 'z) (app 'P 'x)))
                          (lam [['px (app 'P 'x)]] 'px))
                     'py))}])

(defn elaborate! [environment surface]
  (let [result (elaborate/core-expression environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Equality surface failed to elaborate"
                      {:surface surface :result result})))
    (:term result)))

(defn add-spec [environment {:keys [name kind universes transparency type value]}]
  (let [type-term (elaborate! environment type)
        value-term (elaborate! environment value)
        dependencies (into (term/constants type-term)
                           (term/constants value-term))]
    (kernel/add-declaration
     environment
     {:rainbow/kind (or kind :theorem)
      :rainbow/aliases #{name}
      :rainbow/universes (vec universes)
      :rainbow/type type-term
      :rainbow/value value-term
      :rainbow/transparency (or transparency :opaque)
      :rainbow/dependencies dependencies
      :rainbow/provenance {:origin :native :module :equality}
      :rainbow/schema-version 1})))

(defn build-environment []
  (let [base (:environment (first-tactic-program/run-corpus))]
    (reduce (fn [environment spec]
              (let [result (add-spec environment spec)]
                (when-not (= :accepted (:status result))
                  (throw (ex-info "Equality declaration rejected"
                                  {:name (:name spec) :result result})))
                (:environment result)))
            base
            (into [equality-definition] theorem-specs))))

(defn report []
  (let [environment (build-environment)]
    {:status :passed
     :definition 'equality/Eq
     :theorems (count theorem-specs)
     :declarations (count (:rainbow.environment/declarations environment))
     :axioms (into {} (map (fn [{:keys [name]}]
                             [name (kernel/axioms environment name)])
                           theorem-specs))}))

(defn -main [& [command path]]
  (case command
    "record" (println (pr-str (persistence/save-environment! (build-environment) path)))
    "replay" (let [result (persistence/load-environment path)]
               (println (pr-str (dissoc result :environment)))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
