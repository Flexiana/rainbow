(ns rainbow.data.inductive
  "Initial validated Bool, Nat, product, and sum inductive blocks."
  (:require [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.term :as term]))

(def zero [:zero])
(def type-level [:succ zero])
(def U [:param 'u])
(def V [:param 'v])

(def bool-spec
  {:block/schema-version 1
   :block/alias 'data/Bool
   :block/universes []
   :block/parameters []
   :block/sort-level type-level
   :block/constructors
   [{:constructor/alias 'data/false :constructor/fields []}
    {:constructor/alias 'data/true :constructor/fields []}]})

(def nat-spec
  {:block/schema-version 1
   :block/alias 'data/Nat
   :block/universes []
   :block/parameters []
   :block/sort-level type-level
   :block/constructors
   [{:constructor/alias 'data/zero :constructor/fields []}
    {:constructor/alias 'data/succ
     :constructor/fields [{:field/name 'predecessor :field/type [:self]}]}]})

(def product-spec
  {:block/schema-version 1
   :block/alias 'data/Product
   :block/universes ['u 'v]
   :block/parameters
   [{:parameter/name 'A :parameter/type [:sort U]}
    {:parameter/name 'B :parameter/type [:sort V]}]
   :block/sort-level [:max U V]
   :block/constructors
   [{:constructor/alias 'data/pair
     :constructor/fields [{:field/name 'first :field/type [:var 'A]}
                          {:field/name 'second :field/type [:var 'B]}]}]})

(def sum-spec
  {:block/schema-version 1
   :block/alias 'data/Sum
   :block/universes ['u 'v]
   :block/parameters
   [{:parameter/name 'A :parameter/type [:sort U]}
    {:parameter/name 'B :parameter/type [:sort V]}]
   :block/sort-level [:max U V]
   :block/constructors
   [{:constructor/alias 'data/left
     :constructor/fields [{:field/name 'value :field/type [:var 'A]}]}
    {:constructor/alias 'data/right
     :constructor/fields [{:field/name 'value :field/type [:var 'B]}]}]})

(def initial-specs [bool-spec nat-spec product-spec sum-spec])

(defn constant [environment alias levels]
  (term/constant (environment/resolve-id environment alias) levels))

(defn apply* [function & arguments]
  (reduce term/application function arguments))

(defn computation-cases [environment]
  (let [one-level type-level
        nat (constant environment 'data/Nat [])
        zero-term (constant environment 'data/zero [])
        successor (constant environment 'data/succ [])
        one (apply* successor zero-term)
        two (apply* successor one)
        nat-motive (term/lambda-term nat nat)
        nat-step (term/lambda-term nat
                                   (term/lambda-term nat
                                                       (apply* successor (term/bound 0))))
        nat-rec (constant environment 'data/Nat.rec [one-level])
        bool (constant environment 'data/Bool [])
        true-term (constant environment 'data/true [])
        bool-rec (constant environment 'data/Bool.rec [one-level])
        bool-expression (apply* bool-rec (term/lambda-term bool nat)
                                zero-term one true-term)
        product (apply* (constant environment 'data/Product [one-level one-level]) nat nat)
        pair (apply* (constant environment 'data/pair [one-level one-level])
                     nat nat zero-term one)
        product-rec (constant environment 'data/Product.rec
                              [one-level one-level one-level])
        product-expression (apply* product-rec nat nat
                                   (term/lambda-term product nat)
                                   (term/lambda-term nat
                                                       (term/lambda-term nat (term/bound 1)))
                                   pair)
        sum (apply* (constant environment 'data/Sum [one-level one-level]) nat nat)
        right (apply* (constant environment 'data/right [one-level one-level]) nat nat one)
        sum-rec (constant environment 'data/Sum.rec [one-level one-level one-level])
        sum-expression (apply* sum-rec nat nat
                               (term/lambda-term sum nat)
                               (term/lambda-term nat (term/bound 0))
                               (term/lambda-term nat (term/bound 0))
                               right)
        nat-expression (apply* nat-rec nat-motive zero-term nat-step two)]
    [{:name 'data/bool-recursor-true :carrier nat
      :expression bool-expression :expected one}
     {:name 'data/nat-recursor-two :carrier nat
      :expression nat-expression :expected two}
     {:name 'data/product-recursor-pair :carrier nat
      :expression product-expression :expected zero-term}
     {:name 'data/sum-recursor-right :carrier nat
      :expression sum-expression :expected one}]))

(defn add-computation-proof [environment {:keys [name carrier expression expected]}]
  (let [equality (constant environment 'equality/Eq [type-level])
        reflexivity (constant environment 'equality/reflexive [type-level])
        type (apply* equality carrier expression expected)
        value (apply* reflexivity carrier expected)]
    (kernel/add-declaration
     environment
     {:rainbow/kind :theorem
      :rainbow/aliases #{name}
      :rainbow/universes []
      :rainbow/type type
      :rainbow/value value
      :rainbow/transparency :opaque
      :rainbow/dependencies (into (term/constants type) (term/constants value))
      :rainbow/provenance {:origin :native :producer :inductive-iota-dogfood}
      :rainbow/schema-version 1})))

(defn base-environment []
  (let [result (persistence/load-environment "artifacts/day6/environment.edn")]
    (when-not (= :replayed (:status result))
      (throw (ex-info "Day-6 environment failed replay" {:result result})))
    (:environment result)))

(defn build-environment []
  (let [with-blocks
        (reduce (fn [current spec]
                  (let [result (kernel/add-inductive-block current spec)]
                    (when-not (= :accepted (:status result))
                      (throw (ex-info "Initial inductive block rejected"
                                      {:alias (:block/alias spec) :result result})))
                    (:environment result)))
                (base-environment)
                initial-specs)]
    (reduce (fn [current computation]
              (let [result (add-computation-proof current computation)]
                (when-not (= :accepted (:status result))
                  (throw (ex-info "Inductive computation proof rejected"
                                  {:name (:name computation) :result result})))
                (:environment result)))
            with-blocks
            (computation-cases with-blocks))))

(defn report []
  (let [environment (build-environment)]
    {:status :passed
     :blocks (count (:rainbow.environment/blocks environment))
     :computation-proofs (count (computation-cases environment))
     :declarations (count (:rainbow.environment/declarations environment))
     :members (into {}
                    (map (fn [spec]
                           [(:block/alias spec)
                            {:id (:rainbow/id
                                  (environment/block
                                   environment
                                   (kernel/inductive-block-id spec)))
                             :constructors (count (:block/constructors spec))}]))
                    initial-specs)
     :axioms (into {} (map (fn [alias] [alias (kernel/axioms environment alias)])
                           '[data/Bool data/Nat data/Product data/Sum
                             data/bool-recursor-true data/nat-recursor-two
                             data/product-recursor-pair data/sum-recursor-right]))}))

(defn -main [& [command path]]
  (case command
    "record" (println (pr-str (persistence/save-environment! (build-environment) path)))
    "replay" (let [result (persistence/load-environment path)]
               (println (pr-str (dissoc result :environment)))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
