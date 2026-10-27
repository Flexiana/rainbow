(ns rainbow.foreign.mathlib-native
  "Proof-redacted Mathlib statement types translated into native Rainbow data.

  This namespace does not import Lean declarations or proof values. Foreign
  constants cross the boundary only through an explicit concept map whose
  targets already exist in the supplied Rainbow environment. The translated
  type is accepted only after the Rainbow kernel confirms that it is a type."
  (:require [clojure.set :as set]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]))

(def default-constant-aliases
  {"And" 'proposition/conjunction
   "And.intro" 'proposition/conjoin
   "And.left" 'proposition/left
   "And.right" 'proposition/right
   "Eq" 'equality/Eq
   "Eq.refl" 'equality/reflexive
   "Exists" 'proposition/existence
   "Exists.elim" 'proposition/use-witness
   "Exists.fst" 'logic/exists-proof-first
   "Exists.intro" 'proposition/witness
   "False" 'proposition/falsity
   "False.elim" 'proposition/explode
   "Function.Bijective" 'function/bijective
   "Function.Injective" 'function/injective
   "Function.Involutive" 'function/involutive
   "Function.Surjective" 'function/surjective
   "Iff" 'proposition/equivalence
   "Iff.intro" 'proposition/equivalence-intro
   "Iff.mp" 'proposition/equivalence-forward
   "Iff.mpr" 'proposition/equivalence-backward
   "Ne" 'equality/inequality
   "Not" 'proposition/negation
   "Or" 'proposition/disjunction
   "Or.elim" 'proposition/use-disjunction
   "Or.inl" 'proposition/left-disjunct
   "Or.inr" 'proposition/right-disjunct
   "True" 'proposition/truth
   "True.intro" 'proposition/trivial
   "ExistsUnique" 'proposition/unique-existence
   "ExistsUnique.elim" 'proposition/use-unique-witness
   "ExistsUnique.intro" 'proposition/unique-witness
   "Nat" 'data/Nat})

(def supported-binder-modes #{:explicit :implicit :instance-implicit})

(defn- reject! [category message data]
  (throw (ex-info message (assoc data :error/category category))))

(defn- expect-form! [expression tag arity path]
  (when-not (and (vector? expression)
                 (= tag (first expression))
                 (= arity (count expression)))
    (reject! :mathlib-native/malformed-expression
             "Foreign expression has the wrong tagged shape"
             {:path path :expected/tag tag :expected/arity arity
              :expression expression})))

(defn- raw-universe-parameters [expression]
  (letfn [(walk [node]
            (if-not (vector? node)
              #{}
              (case (first node)
                :param (if (string? (second node)) #{(second node)} #{})
                :zero #{}
                (:succ :sort) (walk (second node))
                :bound #{}
                :const (into #{} (mapcat walk (nth node 2 [])))
                (:max :imax :app :lam :pi) (into (walk (second node)) (walk (nth node 2 nil)))
                :let (into (walk (second node))
                           (into (walk (nth node 2 nil))
                                 (walk (nth node 3 nil))))
                #{})))]
    (walk expression)))

(defn- raw-constant-names [expression]
  (letfn [(walk [node]
            (if-not (vector? node)
              #{}
              (case (first node)
                :const (if (string? (second node)) #{(second node)} #{})
                (:app :lam :pi) (into (walk (second node)) (walk (nth node 2 nil)))
                :let (into (walk (second node))
                           (into (walk (nth node 2 nil))
                                 (walk (nth node 3 nil))))
                #{})))]
    (walk expression)))

(defn- statement-universes [statement]
  (let [raw (raw-universe-parameters (:foreign/type statement))
        emitted (:foreign/universes statement)
        names (if (nil? emitted) (vec (sort raw)) emitted)]
    (when-not (and (vector? names)
                   (every? #(and (string? %) (not (empty? %))) names)
                   (= (count names) (count (distinct names))))
      (reject! :mathlib-native/invalid-universes
               "Statement universes must be distinct non-empty strings"
               {:foreign/name (:foreign/name statement)
                :foreign/universes emitted}))
    (let [declared (set names)
          unbound (set/difference raw declared)]
      (when (seq unbound)
        (reject! :mathlib-native/unbound-universe
                 "Statement type refers to an undeclared universe"
                 {:foreign/name (:foreign/name statement)
                  :unbound unbound :declared declared})))
    (mapv symbol names)))

(defn- translate-level [level universe-names path]
  (when-not (vector? level)
    (reject! :mathlib-native/malformed-level
             "Foreign universe level must be tagged data"
             {:path path :level level}))
  (case (first level)
    :zero (do (expect-form! level :zero 1 path) [:zero])
    :param
    (do
      (expect-form! level :param 2 path)
      (let [raw-name (second level)
            name (when (string? raw-name) (symbol raw-name))]
        (when-not (and name (contains? universe-names name))
          (reject! :mathlib-native/unbound-universe
                   "Foreign universe parameter is absent from the statement"
                   {:path path :level level :declared universe-names}))
        [:param name]))
    :succ
    (do (expect-form! level :succ 2 path)
        [:succ (translate-level (second level) universe-names (conj path 1))])
    :max
    (do (expect-form! level :max 3 path)
        [:max (translate-level (second level) universe-names (conj path 1))
         (translate-level (nth level 2) universe-names (conj path 2))])
    :imax
    (do (expect-form! level :imax 3 path)
        [:imax (translate-level (second level) universe-names (conj path 1))
         (translate-level (nth level 2) universe-names (conj path 2))])
    (reject! :mathlib-native/unsupported-level
             "Foreign universe level is outside Rainbow's supported fragment"
             {:path path :level level :constructor (first level)})))

(defn- native-concept [constant-aliases name]
  (let [mapping (get constant-aliases name)]
    (cond
      (symbol? mapping) {:native/alias mapping :native/level-transform :identity}
      (map? mapping) mapping)))

(defn- resolve-native-constant [checked-environment constant-aliases name path]
  (let [concept (native-concept constant-aliases name)
        alias (:native/alias concept)
        id (when alias (environment/resolve-id checked-environment alias))]
    (when-not concept
      (reject! :mathlib-native/unknown-constant
               "Foreign constant has no native concept mapping"
               {:path path :foreign/name name}))
    (when-not (and (symbol? alias)
                   (contains? #{nil :identity :successor
                                :lean-set-range}
                              (:native/level-transform concept)))
      (reject! :mathlib-native/invalid-concept-map
               "Native concept mapping has an invalid level transform"
               {:path path :foreign/name name :mapping concept}))
    (when-not id
      (reject! :mathlib-native/missing-native-concept
               "Mapped native concept is absent from the Rainbow environment"
               {:path path :foreign/name name :native/alias alias}))
    (assoc concept :native/id id)))

(defn- transform-levels [concept levels]
  (case (:native/level-transform concept)
    :successor (mapv (fn [level] [:succ level]) levels)
    :lean-set-range
    (let [[codomain-level domain-sort-level] levels]
      (when-not (and (= 2 (count levels))
                     (= :succ (first domain-sort-level)))
        (reject! :mathlib-native/unsupported-set-range-levels
                 "Native Set.range currently requires a Type-valued domain"
                 {:foreign/levels levels
                  :native/alias (:native/alias concept)}))
      [(second domain-sort-level) codomain-level])
    levels))

;; -- Narrow typed-literal bridge -------------------------------------------
;;
;; Lean elaborates the numeral `(0 : Nat)` to the fully applied instance term
;; `@OfNat.ofNat Nat (Lean.Literal.natVal 0) (instOfNatNat 0)`. The proof-
;; redacted exporter cannot represent the raw `Lean.Literal.natVal 0` inside
;; Rainbow's term fragment, so it emits it as the tagged placeholder node
;; `[:unsupported :literal "Lean.Literal.natVal 0"]`. Rainbow has no general
;; literal evaluator and deliberately keeps one out of the trusted boundary.
;; Instead this bridge recognizes exactly that one closed application shape and
;; rewrites it to the native `data/zero` constructor. Nothing else about the
;; kernel or the supported term fragment changes: a bare placeholder, a non-Nat
;; OfNat, a nonzero value, or a malformed spine are all rejected with a precise
;; category rather than silently mistranslated.

(def ^:private nat-literal-constant "OfNat.ofNat")
(def ^:private nat-instance-constant "instOfNatNat")
(def ^:private nat-type-constant "Nat")
(def ^:private nat-zero-literal-description "Lean.Literal.natVal 0")

;; The exact frozen sub-terms of `(0 : Nat)`, compared structurally (levels and
;; instance argument included) so a mismatched instance payload, an extra
;; instance application, or a wrong OfNat universe level cannot slip through.
(def ^:private nat-zero-literal
  [:unsupported :literal nat-zero-literal-description])
(def ^:private nat-zero-head
  [:const nat-literal-constant [[:zero]]])
(def ^:private nat-zero-instance
  [:app [:const nat-instance-constant []] nat-zero-literal])
(def ^:private nat-carrier-type
  [:const nat-type-constant []])

(defn- application-head-name
  "Peels a left-nested application spine and returns the head `:const` name, or
  nil when the head is not a named constant."
  [expression]
  (loop [node expression]
    (cond
      (not (vector? node)) nil
      (= :app (first node)) (recur (second node))
      (= :const (first node)) (let [name (second node)]
                                (when (string? name) name)))))

(defn- typed-nat-literal-form?
  "True when `expression` is an application spine whose head constant is
  `OfNat.ofNat`. Such a term is a typed numeral and is routed to the narrow
  bridge (which then either rewrites it or rejects it precisely)."
  [expression]
  (and (vector? expression)
       (= :app (first expression))
       (= nat-literal-constant (application-head-name expression))))

(defn- rewrite-typed-nat-literal
  "Rewrites the exact typed Nat-zero form
  `@OfNat.ofNat Nat (natVal 0) instOfNatNat` to the native `data/zero`
  constant. This is a shape-directed bridge, not a literal evaluator: only the
  Nat type, only the value 0, and only the canonical `instOfNatNat` instance
  are accepted."
  [checked-environment expression path]
  (let [reject-shape
        (fn []
          (reject! :mathlib-native/malformed-nat-literal
                   "Typed Nat literal is not the expected OfNat.ofNat application"
                   {:path path :expression expression}))]
    (when-not (and (vector? expression) (= :app (first expression))
                   (= 3 (count expression)))
      (reject-shape))
    (let [instance (nth expression 2)
          applied-to-literal (second expression)]
      (when-not (and (vector? applied-to-literal)
                     (= :app (first applied-to-literal))
                     (= 3 (count applied-to-literal)))
        (reject-shape))
      (let [literal (nth applied-to-literal 2)
            applied-to-type (second applied-to-literal)]
        (when-not (and (vector? applied-to-type)
                       (= :app (first applied-to-type))
                       (= 3 (count applied-to-type)))
          (reject-shape))
        (let [type-argument (nth applied-to-type 2)
              head (second applied-to-type)]
          ;; Exact OfNat.ofNat head, universe levels included.
          (when-not (= nat-zero-head head)
            (reject-shape))
          (when-not (= nat-carrier-type type-argument)
            (reject! :mathlib-native/unsupported-literal-type
                     "The native literal bridge only supports Nat-typed numerals"
                     {:path path :type type-argument}))
          ;; Exact Lean.Literal.natVal 0 placeholder (rejects nonzero and other kinds).
          (when-not (= nat-zero-literal literal)
            (reject! :mathlib-native/unsupported-literal-value
                     "The native literal bridge only supports the Nat value 0 (Lean.Literal.natVal 0)"
                     {:path path :literal literal}))
          ;; Exact `instOfNatNat <literal>` instance -- no mismatched payload, no
          ;; extra application, no alternative instance.
          (when-not (= nat-zero-instance instance)
            (reject! :mathlib-native/unsupported-literal-instance
                     "The native Nat numeral requires exactly (instOfNatNat (Lean.Literal.natVal 0))"
                     {:path path :instance instance}))
          (let [zero-id (environment/resolve-id checked-environment 'data/zero)]
            (when-not zero-id
              (reject! :mathlib-native/missing-native-concept
                       "Native data/zero is absent from the Rainbow environment"
                       {:path path :native/alias 'data/zero}))
            [:const zero-id []]))))))

(declare translate-expression)

(defn- translate-expression
  [checked-environment constant-aliases expression universe-names path]
  (when-not (vector? expression)
    (reject! :mathlib-native/malformed-expression
             "Foreign expression must be tagged data"
             {:path path :expression expression}))
  (case (first expression)
    :sort
    (do (expect-form! expression :sort 2 path)
        [:sort (translate-level (second expression) universe-names
                                (conj path 1))])

    :bound
    (do
      (expect-form! expression :bound 2 path)
      (let [index (second expression)]
        (when-not (and (integer? index) (not (neg? index)))
          (reject! :mathlib-native/malformed-bound
                   "Foreign bound index must be a natural number"
                   {:path (conj path 1) :index index}))
        [:bound index]))

    :const
    (do
      (expect-form! expression :const 3 path)
      (let [name (second expression)
            levels (nth expression 2)]
        (when-not (and (string? name) (vector? levels))
          (reject! :mathlib-native/malformed-constant
                   "Foreign constant requires a string name and level vector"
                   {:path path :expression expression}))
        (let [concept
              (resolve-native-constant checked-environment constant-aliases name
                                       (conj path 1))
              translated
              (mapv (fn [index level]
                      (translate-level level universe-names
                                       (conj path 2 index)))
                    (range) levels)]
          [:const (:native/id concept)
           (transform-levels concept translated)])))

    :app
    (if (typed-nat-literal-form? expression)
      (rewrite-typed-nat-literal checked-environment expression path)
      (do (expect-form! expression :app 3 path)
          [:app
           (translate-expression checked-environment constant-aliases
                                 (second expression) universe-names (conj path 1))
           (translate-expression checked-environment constant-aliases
                                 (nth expression 2) universe-names (conj path 2))]))

    :unsupported
    (reject! :mathlib-native/unsupported-literal
             "Exported unsupported Lean nodes have no native evaluator; only the typed Nat zero numeral is bridged"
             {:path path :expression expression})

    (:lam :pi)
    (do
      (expect-form! expression (first expression) 4 path)
      (let [mode (nth expression 3)]
        (when-not (contains? supported-binder-modes mode)
          (reject! :mathlib-native/unsupported-binder
                   "Rainbow currently supports explicit, ordinary implicit, and instance-implicit binders"
                   {:path (conj path 3) :binder mode}))
        [(first expression)
         (translate-expression checked-environment constant-aliases
                               (second expression) universe-names (conj path 1))
         (translate-expression checked-environment constant-aliases
                               (nth expression 2) universe-names (conj path 2))
         (if (= :instance-implicit mode) :implicit mode)]))

    :let
    (do (expect-form! expression :let 4 path)
        [:let
         (translate-expression checked-environment constant-aliases
                               (second expression) universe-names (conj path 1))
         (translate-expression checked-environment constant-aliases
                               (nth expression 2) universe-names (conj path 2))
         (translate-expression checked-environment constant-aliases
                               (nth expression 3) universe-names (conj path 3))])

    (reject! :mathlib-native/unsupported-expression
             "Foreign expression constructor is outside the supported fragment"
             {:path path :expression expression :constructor (first expression)})))

(defn nativeize-statement-type
  "Translates one proof-redacted Mathlib statement into a checked native type.

  Options may supply a complete `:constant-aliases` map. The default native
  logical concept map is used when omitted."
  ([checked-environment statement]
   (nativeize-statement-type checked-environment statement {}))
  ([checked-environment statement {:keys [constant-aliases]
                                   :or {constant-aliases default-constant-aliases}}]
   (try
     (when-not (= :redacted (:foreign/value statement))
       (reject! :mathlib-native/proof-not-redacted
                "Native proving accepts statement types but never Lean proof values"
                {:foreign/name (:foreign/name statement)}))
     (let [universes (statement-universes statement)
           universe-names (set universes)
           type (translate-expression
                 checked-environment constant-aliases (:foreign/type statement)
                 universe-names [:foreign/type])
           _ (term/assert-term! type)
           inferred (kernel/infer checked-environment type universe-names)
           normalized (when (= :checked (:status inferred))
                        (kernel/normalize checked-environment (:type inferred)))]
       (when-not (= :checked (:status inferred))
         (reject! :mathlib-native/kernel-rejected
                  "Nativeized statement is not well typed"
                  {:foreign/name (:foreign/name statement) :kernel inferred}))
       (when-not (and (= :normalized (:status normalized))
                      (= :sort (first (:term normalized))))
         (reject! :mathlib-native/not-a-type
                  "Nativeized statement does not inhabit a universe"
                  {:foreign/name (:foreign/name statement)
                   :kernel inferred :normalized normalized}))
       {:status :nativeized
        :foreign/name (:foreign/name statement)
        :foreign/type-fingerprint (:foreign/type-fingerprint statement)
        :foreign/constants (vec (sort (raw-constant-names
                                       (:foreign/type statement))))
        :universes universes
        :type type
        :kernel {:status :checked :sort (:term normalized)}
        :proof-source :independent-rainbow-search})
     (catch clojure.lang.ExceptionInfo exception
       {:status :rejected
        :foreign/name (:foreign/name statement)
        :error (ex-data exception)
        :message (ex-message exception)}))))
