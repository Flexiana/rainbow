(ns rainbow.kernel
  "Small trusted checker for Rainbow's initial dependent-function calculus."
  (:refer-clojure :exclude [check])
  (:require [clojure.set :as set]
            [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.term :as term]))

(def ^:dynamic *reduction-budget* 1000000)
(def ^:dynamic ^:private *normalization-cache* nil)

(defn- reject! [category message data]
  (throw (ex-info message (assoc data :error/category category))))

(defn- consume [fuel operation]
  (if (pos? fuel)
    (dec fuel)
    (reject! :kernel/resource-limit
             "Kernel reduction budget exhausted"
             {:operation operation})))

(defn- unfoldable? [declaration]
  (and (:rainbow/value declaration)
       (contains? #{:reducible :semireducible}
                  (:rainbow/transparency declaration))))

(declare whnf*)

(defn- application-spine [expression]
  (loop [current expression
         arguments []]
    (if (= :app (first current))
      (recur (second current) (into [(nth current 2)] arguments))
      [current arguments])))

(defn- apply-arguments [function arguments]
  (reduce term/application function arguments))

(defn- recursor-step [environment expression fuel unfolding]
  (let [[head arguments] (application-spine expression)
        declaration (when (= :const (first head))
                      (environment/declaration environment (second head)))]
    (when (= :recursor (:rainbow/kind declaration))
      (let [{:keys [parameter-count constructor-count block-id]}
            (:rainbow/recursor declaration)
            target-index (+ parameter-count 1 constructor-count)
            needed (inc target-index)]
        (when (<= needed (count arguments))
          (let [target (nth arguments target-index)
                [target-head remaining] (whnf* environment target fuel unfolding)
                normalized-expression (apply-arguments
                                       head (assoc arguments target-index target-head))
                [constructor-head constructor-arguments]
                (application-spine target-head)
                constructor (when (= :const (first constructor-head))
                              (environment/declaration environment
                                                       (second constructor-head)))]
            (if-not (and (= :constructor (:rainbow/kind constructor))
                         (= block-id (:rainbow/block-id constructor)))
              [normalized-expression remaining false]
              (let [{constructor-index :index
                     recursive-fields :recursive-fields
                     field-count :field-count}
                    (:rainbow/constructor constructor)
                    field-arguments (vec (take field-count
                                               (drop parameter-count
                                                     constructor-arguments)))
                    _ (when-not (= field-count (count field-arguments))
                        (reject! :kernel/malformed-constructor-application
                                 "Constructor has too few field arguments"
                                 {:constructor (:rainbow/id constructor)
                                  :expected field-count
                                  :actual (count field-arguments)}))
                    case-term (nth arguments (+ parameter-count 1 constructor-index))
                    prefix (subvec arguments 0 (+ parameter-count 1 constructor-count))
                    reduced (reduce (fn [result [field recursive?]]
                                      (let [with-field (term/application result field)]
                                        (if recursive?
                                          (term/application
                                           with-field
                                           (apply-arguments head (conj prefix field)))
                                          with-field)))
                                    case-term
                                    (map vector field-arguments recursive-fields))
                    with-extra (apply-arguments reduced (drop needed arguments))]
                [with-extra (consume remaining :iota) true]))))))))

(defn- whnf*
  [environment expression fuel unfolding]
  (case (first expression)
    :let (recur environment
                (term/instantiate (nth expression 3) (nth expression 2))
                (consume fuel :zeta)
                unfolding)

    :const (let [id (second expression)
                 declaration (environment/declaration environment id)]
             (when-not declaration
               (reject! :kernel/unknown-constant "Unknown constant" {:constant/id id}))
             (if (unfoldable? declaration)
               (do
                 (when (contains? unfolding id)
                   (reject! :kernel/cyclic-reduction
                            "Cyclic transparent definition"
                            {:constant/id id :unfolding unfolding}))
                 (let [parameters (:rainbow/universes declaration)
                       arguments (nth expression 2)]
                   (when-not (= (count parameters) (count arguments))
                     (reject! :kernel/universe-arity
                              "Wrong number of universe arguments"
                              {:constant/id id
                               :expected (count parameters)
                               :actual (count arguments)}))
                   (recur environment
                          (term/instantiate-universes
                           (:rainbow/value declaration)
                           (zipmap parameters arguments))
                          (consume fuel :delta)
                          (conj unfolding id))))
               [expression fuel]))

    :app (let [[function remaining] (whnf* environment (second expression) fuel unfolding)]
           (if (= :lam (first function))
             (recur environment
                    (term/instantiate (nth function 2) (nth expression 2))
                    (consume remaining :beta)
                    unfolding)
             (let [rebuilt [:app function (nth expression 2)]
                   step (recursor-step environment rebuilt remaining unfolding)]
               (if step
                 (let [[next-expression next-fuel reduced?] step]
                   (if reduced?
                     (recur environment next-expression next-fuel unfolding)
                     [next-expression next-fuel]))
                 [rebuilt remaining]))))

    [expression fuel]))

(declare normalize*)

(defn- normalize-uncached*
  [environment expression fuel]
  (let [[head fuel] (whnf* environment expression fuel #{})]
    (case (first head)
      :sort [[:sort (term/normalize-level (second head))] fuel]
      (:bound :const) [head fuel]
      :app (let [[function fuel] (normalize* environment (second head) fuel)
                 [argument fuel] (normalize* environment (nth head 2) fuel)]
             [[:app function argument] fuel])
      :lam (let [[domain fuel] (normalize* environment (second head) fuel)
                 [body fuel] (normalize* environment (nth head 2) fuel)
                 candidate [:lam domain body (nth head 3)]]
             ;; Supported eta: (fn [x] (f x)) = f when x is not free in f.
             (if (and (= :app (first body))
                      (= [:bound 0] (nth body 2)))
               (try
                 [(term/shift (second body) -1) (consume fuel :eta)]
                 (catch clojure.lang.ExceptionInfo _ [candidate fuel]))
               [candidate fuel]))
      :pi (let [[domain fuel] (normalize* environment (second head) fuel)
                [body fuel] (normalize* environment (nth head 2) fuel)]
            [[:pi domain body (nth head 3)] fuel])
      :let (throw (AssertionError. "whnf must eliminate lets")))))

(defn- normalize*
  [environment expression fuel]
  (if-let [entry (and *normalization-cache*
                      (find @*normalization-cache* expression))]
    [(val entry) fuel]
    (let [[normal remaining] (normalize-uncached* environment expression fuel)]
      (when *normalization-cache*
        (swap! *normalization-cache* assoc expression normal))
      [normal remaining])))

(defn normalize
  ([environment expression] (normalize environment expression nil))
  ([environment expression options]
   (try
     (term/assert-term! expression)
     (let [budget (get options :reductions *reduction-budget*)
           cache (or *normalization-cache* (atom {}))
           [normal remaining]
           (binding [*normalization-cache* cache]
             (normalize* environment expression budget))]
       {:status :normalized :term normal :reductions (- budget remaining)})
     (catch clojure.lang.ExceptionInfo exception
       {:status (if (= :kernel/resource-limit (:error/category (ex-data exception)))
                  :resource-limit
                  :rejected)
        :error (ex-data exception)
        :message (ex-message exception)}))))

(defn- normal-form! [environment expression]
  (let [result (normalize environment expression {:reductions *reduction-budget*})]
    (if (= :normalized (:status result))
      (:term result)
      (reject! (get-in result [:error :error/category])
               (:message result)
               (:error result)))))

(defn- definitionally-equal!* [environment left right]
  ;; Reflexivity is free. For non-identical terms the historical normal-form
  ;; comparison is unchanged, but both sides share memoized immutable subterms.
  (or (= left right)
      (binding [*normalization-cache* (atom {})]
        (= (normal-form! environment left)
           (normal-form! environment right)))))

(defn definitionally-equal?
  ([environment left right] (definitionally-equal? environment left right nil))
  ([environment left right _type]
   (try
     (term/assert-term! left)
     (term/assert-term! right)
     (definitionally-equal!* environment left right)
     (catch clojure.lang.ExceptionInfo exception
       (if (= :kernel/resource-limit (:error/category (ex-data exception)))
         {:status :resource-limit :error (ex-data exception)}
         false)))))

(defn- assert-level-scope! [level universe-parameters]
  (let [unknown (set/difference (term/level-params level) universe-parameters)]
    (when (seq unknown)
      (reject! :kernel/unbound-universe
               "Universe parameter is not declared"
               {:unknown unknown :allowed universe-parameters}))))

(defn- assert-term-level-scope! [expression universe-parameters]
  (case (first expression)
    :sort (assert-level-scope! (second expression) universe-parameters)
    :bound nil
    :const (doseq [level (nth expression 2)]
             (assert-level-scope! level universe-parameters))
    :app (do (assert-term-level-scope! (second expression) universe-parameters)
             (assert-term-level-scope! (nth expression 2) universe-parameters))
    (:lam :pi) (do (assert-term-level-scope! (second expression) universe-parameters)
                   (assert-term-level-scope! (nth expression 2) universe-parameters))
    :let (do (assert-term-level-scope! (second expression) universe-parameters)
             (assert-term-level-scope! (nth expression 2) universe-parameters)
             (assert-term-level-scope! (nth expression 3) universe-parameters))))

(declare infer*)

(defn- sort-level! [environment type]
  (let [head (first (whnf* environment type *reduction-budget* #{}))]
    (if (= :sort (first head))
      (second head)
      (reject! :kernel/expected-sort
               "Expected a type whose type is a sort"
               {:actual type :actual-normal head}))))

(defn- check* [environment context expression expected]
  (if (and (= :lam (first expression))
           (= :pi (first (first (whnf* environment expected
                                        *reduction-budget* #{})))))
    (let [expected-pi (first (whnf* environment expected *reduction-budget* #{}))
          actual-domain (second expression)
          expected-domain (second expected-pi)]
      (when-not (= (nth expression 3) (nth expected-pi 3))
        (reject! :kernel/binder-mode-mismatch
                 "Lambda binder mode differs from expected Pi binder"
                 {:expected (nth expected-pi 3) :actual (nth expression 3)}))
      (when-not (definitionally-equal!* environment actual-domain expected-domain)
        (reject! :kernel/type-mismatch
                 "Lambda domain does not match expected Pi domain"
                 {:expected expected-domain :actual actual-domain}))
      (sort-level! environment (infer* environment context actual-domain))
      (check* environment
              (into [actual-domain] context)
              (nth expression 2)
              (nth expected-pi 2)))
    (let [actual (infer* environment context expression)]
      (when-not (definitionally-equal!* environment actual expected)
        (reject! :kernel/type-mismatch
                 "Term does not inhabit expected type"
                 {:expected expected :actual actual :term expression}))))
  expression)

(defn- infer-constant [environment id levels]
  (let [declaration (environment/declaration environment id)]
    (when-not declaration
      (reject! :kernel/unknown-constant "Unknown constant" {:constant/id id}))
    (let [parameters (:rainbow/universes declaration)]
      (when-not (= (count parameters) (count levels))
        (reject! :kernel/universe-arity
                 "Wrong number of universe arguments"
                 {:constant/id id :expected (count parameters) :actual (count levels)}))
      (term/instantiate-universes (:rainbow/type declaration)
                                  (zipmap parameters levels)))))

(defn- infer* [environment context expression]
  (case (first expression)
    :sort [:sort [:succ (second expression)]]

    :bound (let [index (second expression)]
             (when-not (< index (count context))
               (reject! :kernel/unbound-variable
                        "de Bruijn index is outside the local context"
                        {:index index :context-size (count context)}))
             (term/shift (nth context index) (inc index)))

    :const (infer-constant environment (second expression) (nth expression 2))

    :app (let [function-type (infer* environment context (second expression))
               function-head (first (whnf* environment function-type
                                            *reduction-budget* #{}))]
           (when-not (= :pi (first function-head))
             (reject! :kernel/not-a-function
                      "Application function does not have a Pi type"
                      {:function (second expression) :type function-type}))
           (check* environment context (nth expression 2) (second function-head))
           (term/instantiate (nth function-head 2) (nth expression 2)))

    :lam (let [domain (second expression)
               _ (sort-level! environment (infer* environment context domain))
               body-type (infer* environment (into [domain] context) (nth expression 2))]
           [:pi domain body-type (nth expression 3)])

    :pi (let [domain (second expression)
              domain-sort (infer* environment context domain)
              domain-level (sort-level! environment domain-sort)
              body-sort (infer* environment (into [domain] context) (nth expression 2))
              body-level (sort-level! environment body-sort)]
          [:sort (term/normalize-level [:imax domain-level body-level])])

    :let (let [declared-type (second expression)
               _ (sort-level! environment (infer* environment context declared-type))
               _ (check* environment context (nth expression 2) declared-type)
               body-type (infer* environment (into [declared-type] context) (nth expression 3))]
           (term/instantiate body-type (nth expression 2)))))

(defn infer
  ([environment expression] (infer environment expression #{}))
  ([environment expression universe-parameters]
   (try
     (term/assert-term! expression)
     (assert-term-level-scope! expression (set universe-parameters))
     {:status :checked
      :term expression
      :type (infer* environment [] expression)}
     (catch clojure.lang.ExceptionInfo exception
       {:status :rejected
        :error (ex-data exception)
        :message (ex-message exception)}))))

(defn check
  ([environment expression expected] (check environment expression expected #{}))
  ([environment expression expected universe-parameters]
   (try
     (term/assert-term! expression)
     (term/assert-term! expected)
     (assert-term-level-scope! expression (set universe-parameters))
     (assert-term-level-scope! expected (set universe-parameters))
     (sort-level! environment (infer* environment [] expected))
     (check* environment [] expression expected)
     {:status :checked :term expression :type expected}
     (catch clojure.lang.ExceptionInfo exception
       {:status :rejected
        :error (ex-data exception)
        :message (ex-message exception)}))))

(defn- declaration-axioms [environment declaration]
  (reduce
   (fn [axioms dependency-id]
     (let [dependency (environment/declaration environment dependency-id)]
       (cond
         (= :axiom (:rainbow/kind dependency)) (conj axioms dependency-id)
         dependency (into axioms (:rainbow/axioms dependency))
         :else axioms)))
   #{}
   (:rainbow/dependencies declaration)))

(defn- validate-declaration! [environment declaration]
  (let [kind (:rainbow/kind declaration)
        universes (:rainbow/universes declaration)
        type (:rainbow/type declaration)
        value (:rainbow/value declaration)]
    (when-not (contains? #{:definition :theorem :axiom} kind)
      (reject! :kernel/unsupported-declaration-kind
               "Unsupported declaration kind in the V0 kernel"
               {:kind kind}))
    (when-not (and (vector? universes)
                   (every? symbol? universes)
                   (= (count universes) (count (distinct universes))))
      (reject! :kernel/invalid-universe-parameters
               "Universe parameters must be a vector of distinct symbols"
               {:universes universes}))
    (term/assert-term! type)
    (when-not (term/closed? type)
      (reject! :kernel/free-variable "Declaration type is not closed" {:term type}))
    (let [type-result (infer environment type (set universes))]
      (when-not (= :checked (:status type-result))
        (reject! :kernel/invalid-declaration-type
                 "Declaration type is not a well-formed type"
                 {:cause type-result}))
      (try
        (sort-level! environment (:type type-result))
        (catch clojure.lang.ExceptionInfo exception
          (reject! :kernel/invalid-declaration-type
                   "Declaration type does not itself inhabit a sort"
                   {:cause (ex-data exception)}))))
    (if (= :axiom kind)
      (when (some? value)
        (reject! :kernel/axiom-has-value "An axiom cannot have a value" {}))
      (do
        (when-not value
          (reject! :kernel/missing-value "Definition or theorem is missing a value" {:kind kind}))
        (term/assert-term! value)
        (when-not (term/closed? value)
          (reject! :kernel/free-variable "Declaration value is not closed" {:term value}))
        (let [check-result (check environment value type (set universes))]
          (when-not (= :checked (:status check-result))
            (reject! :kernel/invalid-declaration-value
                     "Declaration value does not inhabit its type"
                     {:cause check-result})))))
    (let [actual-dependencies (into (term/constants type)
                                    (if value (term/constants value) #{}))]
      (when-not (= actual-dependencies (:rainbow/dependencies declaration))
        (reject! :kernel/dependency-mismatch
                 "Declared dependencies differ from term dependencies"
                 {:declared (:rainbow/dependencies declaration)
                  :actual actual-dependencies})))
    declaration))

(defn add-declaration
  "Validates a declaration and returns {:status :accepted :environment ... :declaration ...}.
  No mutable registry is consulted or changed."
  [environment candidate]
  (try
    (when (:rainbow/block-id candidate)
      (reject! :kernel/standalone-block-member
               "Inductive block members must be added atomically" {}))
    (when-not (= environment/schema-version
                 (:rainbow.environment/schema-version environment))
      (reject! :kernel/environment-schema "Unsupported environment schema" {}))
    (let [base (merge {:rainbow/universes []
                       :rainbow/value nil
                       :rainbow/transparency :opaque
                       :rainbow/dependencies #{}
                       :rainbow/aliases #{}
                       :rainbow/schema-version 1}
                      candidate)
          _ (when-not (= 1 (:rainbow/schema-version base))
              (reject! :kernel/declaration-schema "Unsupported declaration schema"
                       {:actual (:rainbow/schema-version base)}))
          _ (when-not (and (set? (:rainbow/aliases base))
                           (every? symbol? (:rainbow/aliases base)))
              (reject! :kernel/invalid-aliases "Aliases must be a set of symbols"
                       {:aliases (:rainbow/aliases base)}))
          _ (when-not (contains? #{:reducible :semireducible :opaque}
                                 (:rainbow/transparency base))
              (reject! :kernel/invalid-transparency "Invalid declaration transparency"
                       {:transparency (:rainbow/transparency base)}))
          _ (validate-declaration! environment base)
          axioms (declaration-axioms environment base)
          semantic (assoc base :rainbow/axioms axioms)
          computed-id (environment/declaration-id semantic)
          supplied-id (:rainbow/id candidate)
          _ (when (and supplied-id (not= supplied-id computed-id))
              (reject! :kernel/forged-declaration-id
                       "Supplied declaration ID does not match semantic content"
                       {:supplied supplied-id :computed computed-id}))
          checked (assoc semantic :rainbow/id computed-id)
          existing (environment/declaration environment computed-id)
          aliases (into (or (:rainbow/aliases existing) #{}) (:rainbow/aliases checked))
          checked (assoc checked :rainbow/aliases aliases)
          alias-conflict (some (fn [alias]
                                 (when-let [old (get-in environment [:rainbow.environment/aliases alias])]
                                   (when (not= old computed-id) [alias old])))
                               aliases)]
      (when alias-conflict
        (reject! :kernel/alias-conflict "Alias already identifies another declaration"
                 {:alias (first alias-conflict) :existing-id (second alias-conflict)}))
      {:status :accepted
       :declaration checked
       :environment (-> environment
                        (assoc-in [:rainbow.environment/declarations computed-id] checked)
                        (update :rainbow.environment/aliases
                                into (zipmap aliases (repeat computed-id)))
                        (cond-> (nil? existing)
                          (update :rainbow.environment/order conj computed-id)))})
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected
       :error (ex-data exception)
       :message (ex-message exception)})))

(def motive-universe-parameter '_rainbow_motive_universe)

(defn- contains-self? [value]
  (cond
    (= [:self] value) true
    (coll? value) (boolean (some contains-self? value))
    :else false))

(defn- normalize-block-level [level universe-index]
  (case (first level)
    :zero [:zero]
    :param (if-some [index (get universe-index (second level))]
             [:parameter index]
             (reject! :kernel/unbound-universe "Block level uses an undeclared universe"
                      {:level level}))
    :succ [:succ (normalize-block-level (second level) universe-index)]
    :max [:max (normalize-block-level (second level) universe-index)
          (normalize-block-level (nth level 2) universe-index)]
    :imax [:imax (normalize-block-level (second level) universe-index)
           (normalize-block-level (nth level 2) universe-index)]))

(defn- validate-block-type-ast!
  "Checks the small named AST used by inductive descriptors before it is
  compiled to de Bruijn core terms. `known` contains parameters and earlier
  constructor fields, so dependent references cannot point forward."
  [ast known universe-parameters]
  (when-not (vector? ast)
    (reject! :kernel/malformed-block-type "Inductive type AST must be a vector"
             {:ast ast}))
  (case (first ast)
    :var
    (when-not (and (= 2 (count ast)) (symbol? (second ast))
                   (contains? known (second ast)))
      (reject! :kernel/unknown-block-variable
               "Inductive type references an unknown or forward variable"
               {:ast ast :known known}))

    :sort
    (do
      (when-not (and (= 2 (count ast)) (term/level? (second ast)))
        (reject! :kernel/malformed-block-type "Malformed sort in inductive type"
                 {:ast ast}))
      (assert-level-scope! (second ast) universe-parameters))

    :const
    (do
      (when-not (and (= 3 (count ast))
                     (or (string? (second ast)) (symbol? (second ast)))
                     (vector? (nth ast 2))
                     (every? term/level? (nth ast 2)))
        (reject! :kernel/malformed-block-type
                 "Malformed constant in inductive type" {:ast ast}))
      (doseq [level (nth ast 2)]
        (assert-level-scope! level universe-parameters)))

    :app
    (do
      (when (< (count ast) 3)
        (reject! :kernel/malformed-block-type
                 "Inductive type application needs an argument" {:ast ast}))
      (doseq [node (rest ast)]
        (validate-block-type-ast! node known universe-parameters)))

    :pi
    (let [[_ bindings body] ast]
      (when-not (and (= 3 (count ast)) (vector? bindings)
                     (every? #(and (vector? %) (= 2 (count %))
                                   (symbol? (first %)))
                             bindings))
        (reject! :kernel/malformed-block-type
                 "Malformed dependent function in inductive type" {:ast ast}))
      (loop [scope known remaining bindings]
        (if-let [[name type-ast] (first remaining)]
          (do (validate-block-type-ast! type-ast scope universe-parameters)
              (recur (conj scope name) (next remaining)))
          (validate-block-type-ast! body scope universe-parameters))))

    (reject! :kernel/malformed-block-type
             "Unsupported node in inductive type AST" {:ast ast}))
  ast)

(defn- normalize-block-type-ast [ast universe-index known]
  (case (first ast)
    :var (or (get known (second ast))
             (reject! :kernel/unknown-block-variable
                      "Unknown variable while normalizing inductive type"
                      {:ast ast :known (keys known)}))
    :sort [:sort (normalize-block-level (second ast) universe-index)]
    :const [:const (second ast)
            (mapv #(normalize-block-level % universe-index) (nth ast 2))]
    :app (into [:app (normalize-block-type-ast (second ast)
                                               universe-index known)]
               (map #(normalize-block-type-ast % universe-index known)
                    (drop 2 ast)))
    :pi (let [[_ bindings body] ast]
          (loop [scope known
                 index 0
                 remaining bindings
                 normalized []]
            (if-let [[name type-ast] (first remaining)]
              (recur (assoc scope name [:bound index])
                     (inc index) (next remaining)
                     (conj normalized
                           (normalize-block-type-ast type-ast universe-index
                                                     scope)))
              [:pi normalized
               (normalize-block-type-ast body universe-index scope)])))
    :self [:self]))

(defn- validate-block-spec! [spec]
  (let [universes (:block/universes spec)
        parameters (:block/parameters spec)
        constructors (:block/constructors spec)
        parameter-names (mapv :parameter/name parameters)
        aliases (into [(:block/alias spec)] (map :constructor/alias constructors))]
    (when-not (= 1 (:block/schema-version spec))
      (reject! :kernel/inductive-schema "Unsupported inductive block schema"
               {:actual (:block/schema-version spec)}))
    (when-not (and (symbol? (:block/alias spec))
                   (vector? universes) (every? symbol? universes)
                   (= (count universes) (count (distinct universes)))
                   (not (some #{motive-universe-parameter} universes)))
      (reject! :kernel/invalid-inductive-header "Malformed inductive block header"
               {:alias (:block/alias spec) :universes universes}))
    (when-not (and (vector? parameters)
                   (every? #(and (symbol? (:parameter/name %))
                                 (vector? (:parameter/type %)))
                           parameters)
                   (= (count parameter-names) (count (distinct parameter-names))))
      (reject! :kernel/invalid-inductive-parameters
               "Inductive parameters must have distinct names and type ASTs"
               {:parameters parameters}))
    (loop [known #{} remaining parameters]
      (when-let [{:parameter/keys [name type]} (first remaining)]
        (validate-block-type-ast! type known (set universes))
        (recur (conj known name) (next remaining))))
    (when-not (and (term/level? (:block/sort-level spec))
                   (seq constructors)
                   (vector? constructors))
      (reject! :kernel/invalid-inductive-result "Malformed inductive result or constructors"
               {:sort-level (:block/sort-level spec)}))
    (assert-level-scope! (:block/sort-level spec) (set universes))
    (when-not (and (every? symbol? aliases)
                   (= (count aliases) (count (distinct aliases))))
      (reject! :kernel/inductive-alias-conflict
               "Inductive and constructor aliases must be distinct symbols"
               {:aliases aliases}))
    (doseq [[constructor-index constructor] (map-indexed vector constructors)]
      (let [fields (:constructor/fields constructor)
            field-names (mapv :field/name fields)]
        (when-not (and (vector? fields)
                       (every? symbol? field-names)
                       (= (count field-names) (count (distinct field-names)))
                       (empty? (set/intersection (set parameter-names) (set field-names))))
          (reject! :kernel/invalid-constructor-fields
                   "Constructor fields must have distinct non-shadowing names"
                   {:constructor constructor-index :fields fields}))
        (loop [known (set parameter-names)
               remaining fields]
          (when-let [field (first remaining)]
            (let [field-type (:field/type field)]
              (cond
                (= [:self] field-type) nil
                (contains-self? field-type)
                (reject! :kernel/non-strictly-positive
                         "Recursive occurrence must be an entire constructor field"
                         {:constructor constructor-index :field field})
                :else (validate-block-type-ast! field-type known
                                                (set universes))))
            (recur (conj known (:field/name field)) (next remaining))))))
    spec))

(defn- semantic-block-spec [spec]
  (let [universes (:block/universes spec)
        universe-index (zipmap universes (range))
        parameters (:block/parameters spec)
        normalized-parameters
        (loop [known {}
               index 0
               remaining parameters
               result []]
          (if-let [{:parameter/keys [name type]} (first remaining)]
            (recur (assoc known name [:parameter index])
                   (inc index) (next remaining)
                   (conj result
                         (normalize-block-type-ast type universe-index known)))
            {:types result :index known}))
        parameter-index (:index normalized-parameters)]
    {:rainbow/kind :inductive-block
     :block/schema-version 1
     :block/universe-count (count universes)
     :block/parameters
     (:types normalized-parameters)
     :block/sort-level (normalize-block-level (:block/sort-level spec) universe-index)
     :block/constructors
     (mapv (fn [constructor]
             (loop [known parameter-index
                    field-index 0
                    remaining (:constructor/fields constructor)
                    result []]
               (if-let [field (first remaining)]
                 (let [field-type (:field/type field)
                       normalized
                       (if (= [:self] field-type)
                         [:self]
                         (normalize-block-type-ast field-type universe-index
                                                   known))]
                   (recur (assoc known (:field/name field) [:field field-index])
                          (inc field-index) (next remaining) (conj result normalized)))
                 result)))
           (:block/constructors spec))}))

(defn inductive-block-id [spec]
  (validate-block-spec! spec)
  (canonical/content-id (semantic-block-spec spec)))

(defn- member-id [block-id member-key]
  (canonical/content-id {:block/id block-id :block/member-key member-key}))

(defn- compile-block-ast [ast context]
  (case (first ast)
    :var (if-some [index (first (keep-indexed (fn [i name]
                                                (when (= name (second ast)) i))
                                              context))]
           (term/bound index)
           (reject! :kernel/unknown-block-variable "Unknown block type variable"
                    {:variable (second ast) :context context}))
    :sort (term/sort-term (second ast))
    :const (term/constant (second ast) (nth ast 2))
    :app (apply-arguments (compile-block-ast (second ast) context)
                          (map #(compile-block-ast % context) (drop 2 ast)))
    :pi (let [[_ bindings body] ast]
          (letfn [(walk [remaining inner-context]
                    (if-let [[name type-ast] (first remaining)]
                      (term/pi-term (compile-block-ast type-ast inner-context)
                                    (walk (next remaining) (into [name] inner-context)))
                      (compile-block-ast body inner-context)))]
            (walk bindings context)))))

(defn- compile-pi [bindings body]
  (letfn [(walk [remaining context]
            (if-let [[name type-ast] (first remaining)]
              (term/pi-term (compile-block-ast type-ast context)
                            (walk (next remaining) (into [name] context)))
              (compile-block-ast body context)))]
    (walk bindings [])))

(defn- app-ast [function arguments]
  (if (seq arguments) (into [:app function] arguments) function))

(defn- block-members [spec block-id]
  (let [universes (:block/universes spec)
        universe-levels (mapv #(vector :param %) universes)
        parameters (:block/parameters spec)
        parameter-bindings (mapv (fn [{:parameter/keys [name type]}] [name type]) parameters)
        parameter-vars (mapv #(vector :var (:parameter/name %)) parameters)
        inductive-id (member-id block-id :inductive)
        inductive-head [:const inductive-id universe-levels]
        inductive-app (app-ast inductive-head parameter-vars)
        constructors (:block/constructors spec)
        constructor-ids (mapv #(member-id block-id [:constructor %])
                              (range (count constructors)))
        inductive-type (compile-pi parameter-bindings
                                   [:sort (:block/sort-level spec)])
        inductive-declaration
        {:rainbow/id inductive-id
         :rainbow/kind :inductive
         :rainbow/aliases #{(:block/alias spec)}
         :rainbow/universes universes
         :rainbow/type inductive-type
         :rainbow/value nil
         :rainbow/transparency :opaque
         :rainbow/dependencies (term/constants inductive-type)
         :rainbow/axioms #{}
         :rainbow/block-id block-id
         :rainbow/member-key :inductive
         :rainbow/schema-version 1}
        constructor-declarations
        (mapv
         (fn [index constructor constructor-id]
           (let [fields (:constructor/fields constructor)
                 field-bindings
                 (mapv (fn [{:field/keys [name type]}]
                         [name (if (= [:self] type) inductive-app type)])
                       fields)
                 constructor-type (compile-pi (into parameter-bindings field-bindings)
                                              inductive-app)]
             {:rainbow/id constructor-id
              :rainbow/kind :constructor
              :rainbow/aliases #{(:constructor/alias constructor)}
              :rainbow/universes universes
              :rainbow/type constructor-type
              :rainbow/value nil
              :rainbow/transparency :opaque
              :rainbow/dependencies (term/constants constructor-type)
              :rainbow/axioms #{}
              :rainbow/block-id block-id
              :rainbow/member-key [:constructor index]
              :rainbow/constructor {:index index
                                    :field-count (count fields)
                                    :recursive-fields (mapv #(= [:self] (:field/type %)) fields)}
              :rainbow/schema-version 1}))
         (range) constructors constructor-ids)
        motive-name '_motive
        target-name '_target
        motive-type [:pi [[target-name inductive-app]]
                     [:sort [:param motive-universe-parameter]]]
        case-bindings
        (mapv
         (fn [constructor-index constructor constructor-id]
           (let [fields (:constructor/fields constructor)
                 bindings
                 (reduce (fn [result [field-index field]]
                           (let [field-name (:field/name field)
                                 recursive? (= [:self] (:field/type field))
                                 field-type (if recursive? inductive-app (:field/type field))
                                 result (conj result [field-name field-type])]
                             (if recursive?
                               (conj result
                                     [(symbol (str "_ih_" constructor-index "_" field-index))
                                      (app-ast [:var motive-name] [[:var field-name]])])
                               result)))
                         [] (map-indexed vector fields))
                 constructor-term (app-ast [:const constructor-id universe-levels]
                                           (into parameter-vars
                                                 (mapv #(vector :var (:field/name %)) fields)))
                 case-type [:pi bindings
                            (app-ast [:var motive-name] [constructor-term])]]
             [(symbol (str "_case_" constructor-index)) case-type]))
         (range) constructors constructor-ids)
        recursor-id (member-id block-id :recursor)
        recursor-universes (conj universes motive-universe-parameter)
        recursor-type
        (compile-pi
         (into parameter-bindings
               (concat [[motive-name motive-type]]
                       case-bindings
                       [[target-name inductive-app]]))
         (app-ast [:var motive-name] [[:var target-name]]))
        recursor-declaration
        {:rainbow/id recursor-id
         :rainbow/kind :recursor
         :rainbow/aliases #{(symbol (str (:block/alias spec) ".rec"))}
         :rainbow/universes recursor-universes
         :rainbow/type recursor-type
         :rainbow/value nil
         :rainbow/transparency :opaque
         :rainbow/dependencies (term/constants recursor-type)
         :rainbow/axioms #{}
         :rainbow/block-id block-id
         :rainbow/member-key :recursor
         :rainbow/recursor {:block-id block-id
                            :parameter-count (count parameters)
                            :constructor-count (count constructors)}
         :rainbow/schema-version 1}]
    {:inductive inductive-declaration
     :constructors constructor-declarations
     :recursor recursor-declaration
     :members (into [inductive-declaration]
                    (conj constructor-declarations recursor-declaration))}))

(defn add-inductive-block [environment spec]
  (try
    (validate-block-spec! spec)
    (let [block-id (inductive-block-id spec)
          supplied-id (:rainbow/id spec)
          _ (when (and supplied-id (not= supplied-id block-id))
              (reject! :kernel/forged-inductive-block-id
                       "Supplied block ID does not match its normalized descriptor"
                       {:supplied supplied-id :computed block-id}))
          {:keys [members] :as generated} (block-members spec block-id)
          aliases (mapcat :rainbow/aliases members)
          conflict (some (fn [alias]
                           (when-let [old (environment/resolve-id environment alias)]
                             [alias old]))
                         aliases)
          _ (when conflict
              (reject! :kernel/alias-conflict "Inductive alias already exists"
                       {:alias (first conflict) :existing-id (second conflict)}))
          block {:rainbow/id block-id
                 :rainbow/kind :inductive-block
                 :block/schema-version 1
                 :block/spec (dissoc spec :rainbow/id)
                 :block/semantic (semantic-block-spec spec)
                 :block/member-ids (mapv :rainbow/id members)}
          staged (-> environment
                     (assoc-in [:rainbow.environment/blocks block-id] block)
                     (update :rainbow.environment/block-order conj block-id)
                     (update :rainbow.environment/declarations
                             into (into {} (map (juxt :rainbow/id identity) members)))
                     (update :rainbow.environment/aliases
                             into (into {} (mapcat (fn [member]
                                                    (map (fn [alias]
                                                           [alias (:rainbow/id member)])
                                                         (:rainbow/aliases member)))
                                                  members)))
                     (update :rainbow.environment/order
                             into (mapv :rainbow/id members)))
          _ (doseq [member members]
              (when-not (= (:rainbow/id member) (environment/declaration-id member))
                (reject! :kernel/inductive-member-id
                         "Generated member ID is inconsistent" {:member member}))
              (term/assert-term! (:rainbow/type member))
              (when-not (term/closed? (:rainbow/type member))
                (reject! :kernel/free-variable "Generated inductive member type is open"
                         {:member (:rainbow/id member)}))
              (let [result (infer staged (:rainbow/type member)
                                  (set (:rainbow/universes member)))]
                (when-not (and (= :checked (:status result))
                               (= :sort (first (:term (normalize staged (:type result))))))
                  (reject! :kernel/invalid-inductive-member-type
                           "Generated inductive member type failed kernel checking"
                           {:member (:rainbow/id member) :cause result}))))]
      {:status :accepted
       :block block
       :declarations members
       :environment staged
       :generated generated})
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected
       :error (ex-data exception)
       :message (ex-message exception)})))

(defn axioms [environment id-or-alias]
  (when-let [id (environment/resolve-id environment id-or-alias)]
    (let [declaration (environment/declaration environment id)]
      (if (= :axiom (:rainbow/kind declaration))
        #{id}
        (:rainbow/axioms declaration)))))
