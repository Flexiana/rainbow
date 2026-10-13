(ns rainbow.history.mathlib-hidden-batch-1
  "First proof-hidden, independently proved Mathlib statement batch."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.equality :as equality]
            [rainbow.term :as term]))

(def report-path "artifacts/day25/report.edn")
(def mathlib-version "v4.30.0")
(def mathlib-commit "c5ea00351c28e24afc9f0f84379aa41082b1188f")
(def source-path "Mathlib/Logic/Function/Basic.lean")
(def source-url
  (str "https://github.com/leanprover-community/mathlib4/blob/"
       mathlib-commit "/" source-path))

(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def sort-u [:sort U])
(def sort-v [:sort V])
(def sort-w [:sort W])

(defn arrow [& values] (into [:->] values))
(defn forall [bindings body] [:forall (vec bindings) body])
(defn lam [bindings body] [:fn (vec bindings) body])
(defn app [function & arguments] (into [:app function] arguments))
(defn const* [alias levels] [:const alias (vec levels)])
(defn eq [level carrier left right]
  (app (const* 'equality/Eq [level]) carrier left right))

(def theorem-specs
  [{:name 'mathlib.function/injective-of-comp
    :foreign/name "Function.Injective.of_comp"
    :universes ['u 'v 'w]
    :type
    (forall [['A sort-u] ['B sort-v] ['C sort-w]
             ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
             ['I (forall [['x 'C] ['y 'C]]
                         (arrow (eq V 'B (app 'f (app 'g 'x))
                                    (app 'f (app 'g 'y)))
                                (eq W 'C 'x 'y)))]
             ['x 'C] ['y 'C] ['h (eq U 'A (app 'g 'x) (app 'g 'y))]]
            (eq W 'C 'x 'y))
    :value
    (lam [['A sort-u] ['B sort-v] ['C sort-w]
          ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
          ['I (forall [['x 'C] ['y 'C]]
                      (arrow (eq V 'B (app 'f (app 'g 'x))
                                 (app 'f (app 'g 'y)))
                             (eq W 'C 'x 'y)))]
          ['x 'C] ['y 'C] ['h (eq U 'A (app 'g 'x) (app 'g 'y))]]
         (app 'I 'x 'y
              (app (const* 'equality/congruent-function [U V])
                   'A 'B 'f (app 'g 'x) (app 'g 'y) 'h)))}

   {:name 'mathlib.function/left-inverse-eq
    :foreign/name "Function.LeftInverse.eq"
    :universes ['u 'v]
    :type (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
                   ['h (forall [['x 'A]] (eq U 'A (app 'g (app 'f 'x)) 'x))]
                   ['x 'A]]
                  (eq U 'A (app 'g (app 'f 'x)) 'x))
    :value (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
                 ['h (forall [['x 'A]] (eq U 'A (app 'g (app 'f 'x)) 'x))]
                 ['x 'A]]
                (app 'h 'x))}

   {:name 'mathlib.function/right-inverse-eq
    :foreign/name "Function.RightInverse.eq"
    :universes ['u 'v]
    :type (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
                   ['h (forall [['x 'B]] (eq V 'B (app 'f (app 'g 'x)) 'x))]
                   ['x 'B]]
                  (eq V 'B (app 'f (app 'g 'x)) 'x))
    :value (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
                 ['h (forall [['x 'B]] (eq V 'B (app 'f (app 'g 'x)) 'x))]
                 ['x 'B]]
                (app 'h 'x))}

   {:name 'mathlib.function/left-inverse-compose
    :foreign/name "Function.LeftInverse.comp"
    :universes ['u 'v 'w]
    :type (forall [['A sort-u] ['B sort-v] ['C sort-w]
                   ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
                   ['h (arrow 'B 'C)] ['i (arrow 'C 'B)]
                   ['hf (forall [['b 'B]] (eq V 'B (app 'f (app 'g 'b)) 'b))]
                   ['hh (forall [['c 'C]] (eq W 'C (app 'h (app 'i 'c)) 'c))]
                   ['c 'C]]
                  (eq W 'C (app 'h (app 'f (app 'g (app 'i 'c)))) 'c))
    :value
    (lam [['A sort-u] ['B sort-v] ['C sort-w]
          ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
          ['h (arrow 'B 'C)] ['i (arrow 'C 'B)]
          ['hf (forall [['b 'B]] (eq V 'B (app 'f (app 'g 'b)) 'b))]
          ['hh (forall [['c 'C]] (eq W 'C (app 'h (app 'i 'c)) 'c))]
          ['c 'C]]
         (app (const* 'equality/transitive [W]) 'C
              (app 'h (app 'f (app 'g (app 'i 'c)))) (app 'h (app 'i 'c)) 'c
              (app (const* 'equality/congruent-function [V W])
                   'B 'C 'h (app 'f (app 'g (app 'i 'c))) (app 'i 'c)
                   (app 'hf (app 'i 'c)))
              (app 'hh 'c)))}

   {:name 'mathlib.function/right-inverse-compose
    :foreign/name "Function.RightInverse.comp"
    :universes ['u 'v 'w]
    :type (forall [['A sort-u] ['B sort-v] ['C sort-w]
                   ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
                   ['h (arrow 'B 'C)] ['i (arrow 'C 'B)]
                   ['hf (forall [['a 'A]] (eq U 'A (app 'g (app 'f 'a)) 'a))]
                   ['hh (forall [['b 'B]] (eq V 'B (app 'i (app 'h 'b)) 'b))]
                   ['a 'A]]
                  (eq U 'A (app 'g (app 'i (app 'h (app 'f 'a)))) 'a))
    :value
    (lam [['A sort-u] ['B sort-v] ['C sort-w]
          ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
          ['h (arrow 'B 'C)] ['i (arrow 'C 'B)]
          ['hf (forall [['a 'A]] (eq U 'A (app 'g (app 'f 'a)) 'a))]
          ['hh (forall [['b 'B]] (eq V 'B (app 'i (app 'h 'b)) 'b))]
          ['a 'A]]
         (app (const* 'equality/transitive [U]) 'A
              (app 'g (app 'i (app 'h (app 'f 'a)))) (app 'g (app 'f 'a)) 'a
              (app (const* 'equality/congruent-function [V U])
                   'B 'A 'g (app 'i (app 'h (app 'f 'a))) (app 'f 'a)
                   (app 'hh (app 'f 'a)))
              (app 'hf 'a)))}])

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Mathlib-derived form failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn build []
  (reduce
   (fn [{:keys [environment results]} spec]
     (let [type (elaborate! environment (:type spec))
           value (elaborate! environment (:value spec))
           added
           (kernel/add-declaration
            environment
            {:rainbow/kind :theorem
             :rainbow/aliases #{(:name spec)}
             :rainbow/universes (:universes spec)
             :rainbow/type type
             :rainbow/value value
             :rainbow/transparency :opaque
             :rainbow/dependencies (into (term/constants type) (term/constants value))
             :rainbow/provenance
             {:origin :native :producer :independent-mathlib-reproof
              :foreign/system :lean :foreign/library :mathlib
              :foreign/version mathlib-version :foreign/commit mathlib-commit
              :foreign/source source-path :foreign/name (:foreign/name spec)
              :foreign/proof-hidden? true}
             :rainbow/schema-version 1})]
       (when-not (= :accepted (:status added))
         (throw (ex-info "Mathlib-derived proof rejected"
                         {:spec (:name spec) :result added})))
       {:environment (:environment added)
        :results (conj results {:spec spec :declaration (:declaration added)})}))
   {:environment (equality/build-environment) :results []}
   theorem-specs))

(defn report []
  (let [{:keys [environment results]} (build)
        ids (mapv #(get-in % [:declaration :rainbow/id]) results)
        names (mapv #(get-in % [:spec :foreign/name]) results)
        axioms (into {} (map (fn [result]
                              [(get-in result [:spec :name])
                               (kernel/axioms environment
                                              (get-in result [:declaration :rainbow/id]))]))
                     results)
        passed? (and (= 5 (count results) (count (distinct ids)))
                     (every? empty? (vals axioms)))
        base {:status (if passed? :passed :failed)
              :source {:library :mathlib :version mathlib-version
                       :commit mathlib-commit :path source-path :url source-url}
              :selection {:foreign-theorems names
                          :lean-proofs-visible-to-rainbow? false
                          :nativeization :expanded-function-predicates
                          :statement-weakened? false}
              :proofs {:checked (count results) :distinct (count (distinct ids))
                       :mappings (mapv (fn [result]
                                        {:foreign/name (get-in result [:spec :foreign/name])
                                         :native/id (get-in result
                                                            [:declaration :rainbow/id])})
                                      results)
                       :axioms axioms}
              :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :mathlib/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command path]]
  (case command
    "hash" (println (:report/id (report)))
    "replay" (let [result (load-report (or path report-path))]
               (println (pr-str result))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
