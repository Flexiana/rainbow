(ns rainbow.data.list
  "Parameterized lists and recursor-defined length, append, and map."
  (:refer-clojure :exclude [list map])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def sort-u [:sort U])
(def sort-v [:sort V])

(defn constant-form [alias levels] [:const alias (vec levels)])
(defn app [function & arguments] (into [:app function] arguments))
(defn forall [bindings body] [:forall (vec bindings) body])
(defn lambda [bindings body] [:fn (vec bindings) body])
(defn arrow [& expressions] (into [:->] expressions))

(defn list-of [level element]
  (app (constant-form 'data/List [level]) element))

(defn nil-of [level element]
  (app (constant-form 'data/nil [level]) element))

(defn cons-of [level element head tail]
  (app (constant-form 'data/cons [level]) element head tail))

(defn eq [level carrier left right]
  (app (constant-form 'equality/Eq [level]) carrier left right))

(def list-spec
  {:block/schema-version 1
   :block/alias 'data/List
   :block/universes ['u]
   :block/parameters
   [{:parameter/name 'A :parameter/type [:sort U]}]
   :block/sort-level U
   :block/constructors
   [{:constructor/alias 'data/nil :constructor/fields []}
    {:constructor/alias 'data/cons
     :constructor/fields [{:field/name 'head :field/type [:var 'A]}
                          {:field/name 'tail :field/type [:self]}]}]})

(def definition-specs
  [{:name 'list/length
    :universes ['u]
    :type (forall [['A sort-u]
                   ['xs (list-of U 'A)]]
                  (constant-form 'data/Nat []))
    :value
    (lambda [['A sort-u]
             ['xs (list-of U 'A)]]
            (app (constant-form 'data/List.rec [U type-level])
                 'A
                 (lambda [['ignored (list-of U 'A)]]
                         (constant-form 'data/Nat []))
                 (constant-form 'data/zero [])
                 (lambda [['head 'A]
                          ['tail (list-of U 'A)]
                          ['induction-hypothesis (constant-form 'data/Nat [])]]
                         (app (constant-form 'data/succ [])
                              'induction-hypothesis))
                 'xs))}

   {:name 'list/append
    :universes ['u]
    :type (forall [['A sort-u]
                   ['xs (list-of U 'A)]
                   ['ys (list-of U 'A)]]
                  (list-of U 'A))
    :value
    (lambda [['A sort-u]
             ['xs (list-of U 'A)]
             ['ys (list-of U 'A)]]
            (app
             (app (constant-form 'data/List.rec [U U])
                  'A
                  (lambda [['ignored (list-of U 'A)]]
                          (arrow (list-of U 'A) (list-of U 'A)))
                  (lambda [['suffix (list-of U 'A)]] 'suffix)
                  (lambda [['head 'A]
                           ['tail (list-of U 'A)]
                           ['induction-hypothesis
                            (arrow (list-of U 'A) (list-of U 'A))]]
                          (lambda [['suffix (list-of U 'A)]]
                                  (cons-of U 'A 'head
                                           (app 'induction-hypothesis 'suffix))))
                  'xs)
             'ys))}

   {:name 'list/map
    :universes ['u 'v]
    :type (forall [['A sort-u]
                   ['B sort-v]
                   ['f (arrow 'A 'B)]
                   ['xs (list-of U 'A)]]
                  (list-of V 'B))
    :value
    (lambda [['A sort-u]
             ['B sort-v]
             ['f (arrow 'A 'B)]
             ['xs (list-of U 'A)]]
            (app (constant-form 'data/List.rec [U V])
                 'A
                 (lambda [['ignored (list-of U 'A)]] (list-of V 'B))
                 (nil-of V 'B)
                 (lambda [['head 'A]
                          ['tail (list-of U 'A)]
                          ['induction-hypothesis (list-of V 'B)]]
                         (cons-of V 'B (app 'f 'head) 'induction-hypothesis))
                 'xs))}])

(defn base-environment []
  (let [result (persistence/load-environment "artifacts/day8/environment.edn")]
    (when-not (= :replayed (:status result))
      (throw (ex-info "Day-8 environment failed replay" {:result result})))
    (:environment result)))

(defn elaborate! [environment surface]
  (let [result (elaborate/core-expression environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "List expression failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn add-list-block [environment]
  (let [result (kernel/add-inductive-block environment list-spec)]
    (when-not (= :accepted (:status result))
      (throw (ex-info "List block rejected" {:result result})))
    (:environment result)))

(defn add-definition [environment {:keys [name universes type value]}]
  (let [core-type (elaborate! environment type)
        core-value (elaborate! environment value)
        result
        (kernel/add-declaration
         environment
         {:rainbow/kind :definition
          :rainbow/aliases #{name}
          :rainbow/universes universes
          :rainbow/type core-type
          :rainbow/value core-value
          :rainbow/transparency :reducible
          :rainbow/dependencies (into (term/constants core-type)
                                      (term/constants core-value))
          :rainbow/provenance {:origin :native
                               :producer :list-structural-recursor}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "List definition rejected" {:name name :result result})))
    (:environment result)))

(defn build-definitions []
  (reduce add-definition (add-list-block (base-environment)) definition-specs))

(defn theorem-specs []
  (let [nat (constant-form 'data/Nat [])
        zero (constant-form 'data/zero [])
        successor (constant-form 'data/succ [])
        list-a (list-of U 'A)
        list-b (list-of V 'B)
        nil-a (nil-of U 'A)
        nil-b (nil-of V 'B)
        append (constant-form 'list/append [U])
        length (constant-form 'list/length [U])
        map-list (constant-form 'list/map [U V])]
    [{:name 'list/length-nil
      :universes ['u]
      :intros 1
      :target (forall [['A sort-u]]
                      (eq type-level nat (app length 'A nil-a) zero))}
     {:name 'list/length-cons
      :universes ['u]
      :intros 3
      :target (forall [['A sort-u] ['head 'A] ['tail list-a]]
                      (eq type-level nat
                          (app length 'A (cons-of U 'A 'head 'tail))
                          (app successor (app length 'A 'tail))))}
     {:name 'list/append-nil-left
      :universes ['u]
      :intros 2
      :target (forall [['A sort-u] ['ys list-a]]
                      (eq U list-a (app append 'A nil-a 'ys) 'ys))}
     {:name 'list/append-cons
      :universes ['u]
      :intros 4
      :target (forall [['A sort-u] ['head 'A] ['tail list-a] ['ys list-a]]
                      (eq U list-a
                          (app append 'A (cons-of U 'A 'head 'tail) 'ys)
                          (cons-of U 'A 'head (app append 'A 'tail 'ys))))}
     {:name 'list/map-nil
      :universes ['u 'v]
      :intros 3
      :target (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]]
                      (eq V list-b (app map-list 'A 'B 'f nil-a) nil-b))}
     {:name 'list/map-cons
      :universes ['u 'v]
      :intros 5
      :target (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
                       ['head 'A] ['tail list-a]]
                      (eq V list-b
                          (app map-list 'A 'B 'f (cons-of U 'A 'head 'tail))
                          (cons-of V 'B (app 'f 'head)
                                   (app map-list 'A 'B 'f 'tail))))}
     {:name 'list/append-nil-right
      :universes ['u]
      :induction true
      :target (forall [['A sort-u] ['xs list-a]]
                      (eq U list-a (app append 'A 'xs nil-a) 'xs))}
     {:name 'list/map-identity
      :universes ['u]
      :induction true
      :target (forall [['A sort-u] ['xs list-a]]
                      (eq U list-a
                          (app (constant-form 'list/map [U U])
                               'A 'A (lambda [['x 'A]] 'x) 'xs)
                          'xs))}]))

(defn prove-reflexive [environment target universes intro-count]
  (let [started (proof/start environment target {:universes universes})
        introduced (tactic/run (:state started)
                               (tactic/repeat (tactic/intro) {:max intro-count}))]
    (tactic/run (:state introduced) (tactic/reflexivity))))

(defn prove-by-induction [environment target universes]
  (let [started (proof/start environment target {:universes universes})
        parameter (tactic/run (:state started) (tactic/intro 'A))
        input (tactic/run (:state parameter) (tactic/intro 'xs))
        induced (tactic/run (:state input) (tactic/induction [:bound 0]))
        nil-case (tactic/run (:state induced) (tactic/reflexivity))
        head (tactic/run (:state nil-case) (tactic/intro 'head))
        tail (tactic/run (:state head) (tactic/intro 'tail))
        hypothesis (tactic/run (:state tail) (tactic/intro 'induction-hypothesis))
        rewritten (tactic/run (:state hypothesis)
                              (tactic/rewrite [:bound 0] {:direction :backward}))]
    (tactic/run (:state rewritten) (tactic/reflexivity))))

(defn prove-theorem [environment spec]
  (let [target (elaborate! environment (:target spec))]
    (if (:induction spec)
      (prove-by-induction environment target (:universes spec))
      (prove-reflexive environment target (:universes spec) (:intros spec)))))

(defn register-theorem [environment spec]
  (let [result (prove-theorem environment spec)]
    (when-not (= :proved (:status result))
      (throw (ex-info "List theorem failed" {:name (:name spec) :result result})))
    (let [type (get-in result [:proof :proof/type])
          value (get-in result [:proof :proof/term])
          declaration-result
          (kernel/add-declaration
           environment
           {:rainbow/kind :theorem
            :rainbow/aliases #{(:name spec)}
            :rainbow/universes (:universes spec)
            :rainbow/type type
            :rainbow/value value
            :rainbow/transparency :opaque
            :rainbow/dependencies (into (term/constants type) (term/constants value))
            :rainbow/provenance {:origin :native :producer :day-9-list}
            :rainbow/schema-version 1})]
      (when-not (= :accepted (:status declaration-result))
        (throw (ex-info "List theorem declaration rejected"
                        {:name (:name spec) :result declaration-result})))
      {:environment (:environment declaration-result)
       :result result
       :declaration (:declaration declaration-result)})))

(defn build []
  (reduce (fn [{:keys [environment results]} spec]
            (let [registered (register-theorem environment spec)]
              {:environment (:environment registered)
               :results (conj results (assoc (dissoc registered :environment)
                                        :name (:name spec)))}))
          {:environment (build-definitions) :results []}
          (theorem-specs)))

(defn nontermination-attempt [environment]
  (let [nat (term/constant (environment/resolve-id environment 'data/Nat) [])
        loop-id "sha256:0000000000000000000000000000000000000000000000000000000000000000"
        type (term/pi-term nat nat)
        value (term/lambda-term nat
                                (term/application (term/constant loop-id [])
                                                  (term/bound 0)))]
    (kernel/add-declaration
     environment
     {:rainbow/id loop-id
      :rainbow/kind :definition
      :rainbow/aliases #{'list/nonterminating-loop}
      :rainbow/universes []
      :rainbow/type type
      :rainbow/value value
      :rainbow/transparency :reducible
      :rainbow/dependencies #{(environment/resolve-id environment 'data/Nat) loop-id}
      :rainbow/schema-version 1})))

(defn report []
  (let [{:keys [environment results]} (build)
        rejected (nontermination-attempt environment)]
    {:status :passed
     :blocks (count (:rainbow.environment/blocks environment))
     :definitions (mapv :name definition-specs)
     :theorems (count results)
     :induction-proofs (count (filter #(some #{:induction}
                                              (clojure.core/map
                                               :event/tactic
                                               (get-in % [:result :proof :proof/history])))
                                      results))
     :events (frequencies
              (mapcat #(clojure.core/map
                        :event/tactic
                        (get-in % [:result :proof :proof/history]))
                      results))
     :declarations (count (:rainbow.environment/declarations environment))
     :nontermination {:status (:status rejected)
                      :category (get-in rejected [:error :error/category])
                      :cause (get-in rejected [:error :cause :error :error/category])}
     :axioms (into {} (clojure.core/map
                       (fn [{:keys [name]}] [name (kernel/axioms environment name)])
                       results))}))

(defn -main [& [command path]]
  (case command
    "record" (println (pr-str (persistence/save-environment! (:environment (build)) path)))
    "replay" (let [result (persistence/load-environment path)]
               (println (pr-str (dissoc result :environment)))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
