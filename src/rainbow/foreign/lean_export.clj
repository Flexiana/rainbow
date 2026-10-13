(ns rainbow.foreign.lean-export
  "Untrusted structural export of checked Rainbow declarations to pinned Lean.

  The exporter never establishes truth: it only renders a declaration already
  accepted by Rainbow.  Lean checks the rendered term, serializes its own Expr,
  and the ordinary foreign importer checks that expression again on return."
  (:require [clojure.string :as string]
            [rainbow.environment :as environment]
            [rainbow.foreign.lean :as lean]
            [rainbow.kernel :as kernel]))

(def ^:private lean-identifier-pattern #"[A-Za-z_][A-Za-z0-9_']*")
(def ^:private lean-qualified-pattern
  #"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*")

(defn- reject! [category message data]
  (throw (ex-info message (assoc data :error/category category))))

(defn- checked-declaration [rainbow-environment id-or-alias]
  (let [id (environment/resolve-id rainbow-environment id-or-alias)
        declaration (some->> id (environment/declaration rainbow-environment))]
    (when-not declaration
      (reject! :lean-export/unknown-declaration
               "Only a declaration already checked into the Rainbow environment can be exported"
               {:declaration id-or-alias}))
    (when-not (and (= id (:rainbow/id declaration))
                   (= id (environment/declaration-id declaration)))
      (reject! :lean-export/forged-declaration
               "Environment entry does not have its claimed semantic declaration identity"
               {:declaration id-or-alias :resolved-id id
                :claimed-id (:rainbow/id declaration)
                :computed-id (environment/declaration-id declaration)}))
    (when-some [value (:rainbow/value declaration)]
      (let [recheck (kernel/check rainbow-environment value
                                  (:rainbow/type declaration)
                                  (set (:rainbow/universes declaration)))]
        (when-not (= :checked (:status recheck))
          (reject! :lean-export/declaration-no-longer-checks
                   "Environment entry failed an export-time Rainbow recheck"
                   {:declaration id-or-alias :cause recheck}))))
    declaration))

(defn- validate-identifier! [category value path]
  (let [rendered (str value)]
    (when-not (re-matches lean-identifier-pattern rendered)
      (reject! category "Value is not a safe Lean identifier"
               {:path path :value value}))
    rendered))

(defn- validate-qualified! [category value path]
  (when-not (and (string? value) (re-matches lean-qualified-pattern value))
    (reject! category "Value is not a safe qualified Lean identifier"
             {:path path :value value}))
  value)

(defn- render-level [level universes path]
  (when-not (vector? level)
    (reject! :lean-export/malformed-level "Rainbow universe level must be tagged data"
             {:path path :level level}))
  (case (first level)
    :zero "0"
    :param (let [name (second level)]
             (when-not (contains? universes name)
               (reject! :lean-export/unbound-universe
                        "Universe parameter is absent from the declaration"
                        {:path path :level level :universes universes}))
             (validate-identifier! :lean-export/unsafe-universe-name name path))
    :succ (str "(" (render-level (second level) universes (conj path 1)) " + 1)")
    :max (str "(max "
              (render-level (second level) universes (conj path 1)) " "
              (render-level (nth level 2 nil) universes (conj path 2)) ")")
    :imax (str "(imax "
               (render-level (second level) universes (conj path 1)) " "
               (render-level (nth level 2 nil) universes (conj path 2)) ")")
    (reject! :lean-export/unsupported-level "Unsupported Rainbow universe level"
             {:path path :level level :constructor (first level)})))

(defn- native-lean-constants [rainbow-environment]
  (reduce-kv
   (fn [result lean-name rainbow-alias]
     (if-let [id (environment/resolve-id rainbow-environment rainbow-alias)]
       (assoc result id lean-name)
       result))
   {} lean/native-constant-aliases))

(declare render-expression)

(defn- render-binder [tag mode name domain body]
  (case [tag mode]
    [:pi :explicit] (str "((" name " : " domain ") → " body ")")
    [:pi :implicit] (str "({" name " : " domain "} → " body ")")
    [:lam :explicit] (str "(fun (" name " : " domain ") => " body ")")
    [:lam :implicit] (str "(fun {" name " : " domain "} => " body ")")
    (reject! :lean-export/unsupported-binder
             "Initial export supports explicit and ordinary implicit binders"
             {:constructor tag :binder mode})))

(defn- render-expression
  [expression context universes constants path]
  (when-not (vector? expression)
    (reject! :lean-export/malformed-expression
             "Rainbow expression must be tagged data"
             {:path path :expression expression}))
  (case (first expression)
    :sort (str "(Sort "
               (render-level (second expression) universes (conj path 1)) ")")
    :bound (let [index (second expression)]
             (when-not (and (integer? index) (<= 0 index) (< index (count context)))
               (reject! :lean-export/unbound-variable
                        "de Bruijn index escapes the current binder context"
                        {:path (conj path 1) :index index
                         :context-depth (count context)}))
             (nth context index))
    :const (let [id (second expression)
                 lean-name (get constants id)
                 levels (nth expression 2 nil)]
             (when-not lean-name
               (reject! :lean-export/unmapped-constant
                        "Rainbow constant has no explicit Lean mapping"
                        {:path (conj path 1) :rainbow/id id}))
             (when-not (vector? levels)
               (reject! :lean-export/malformed-constant
                        "Constant universe instantiation must be a vector"
                        {:path (conj path 2) :levels levels}))
             (str lean-name
                  (when (seq levels)
                    (str ".{" (string/join ", "
                                           (map-indexed
                                            (fn [index level]
                                              (render-level level universes
                                                            (conj path 2 index)))
                                            levels)) "}"))))
    :app (str "("
              (render-expression (second expression) context universes constants
                                 (conj path 1))
              " "
              (render-expression (nth expression 2 nil) context universes constants
                                 (conj path 2))
              ")")
    (:pi :lam)
    (let [tag (first expression)
          mode (nth expression 3 nil)
          name (str "x" (count context))
          domain (render-expression (second expression) context universes constants
                                    (conj path 1))
          body (render-expression (nth expression 2 nil) (into [name] context)
                                  universes constants (conj path 2))]
      (try
        (render-binder tag mode name domain body)
        (catch clojure.lang.ExceptionInfo exception
          (throw (ex-info (ex-message exception)
                          (assoc (ex-data exception) :path (conj path 3)))))))
    :let (let [name (str "x" (count context))
               type (render-expression (second expression) context universes constants
                                       (conj path 1))
               value (render-expression (nth expression 2 nil) context universes constants
                                        (conj path 2))
               body (render-expression (nth expression 3 nil) (into [name] context)
                                       universes constants (conj path 3))]
           (str "(let " name " : " type " := " value "; " body ")"))
    (reject! :lean-export/unsupported-expression
             "Unsupported Rainbow expression constructor"
             {:path path :expression expression :constructor (first expression)})))

(def ^:private neutral-exporter-source
  (str
   "private def quoteString (value : String) : String := toString (repr value)\n\n"
   "private partial def levelEDN : Level → String\n"
   "  | .zero => \"[:zero]\"\n"
   "  | .succ level => s!\"[:succ {levelEDN level}]\"\n"
   "  | .max left right => s!\"[:max {levelEDN left} {levelEDN right}]\"\n"
   "  | .imax left right => s!\"[:imax {levelEDN left} {levelEDN right}]\"\n"
   "  | .param name => s!\"[:param {quoteString name.toString}]\"\n"
   "  | .mvar id => s!\"[:unsupported-level :mvar {quoteString (toString (repr id))}]\"\n\n"
   "private def binderEDN : BinderInfo → String\n"
   "  | .default => \":explicit\"\n"
   "  | .implicit => \":implicit\"\n"
   "  | .strictImplicit => \":strict-implicit\"\n"
   "  | .instImplicit => \":instance-implicit\"\n\n"
   "private partial def exprEDN : Expr → String\n"
   "  | .bvar index => s!\"[:bound {index}]\"\n"
   "  | .sort level => s!\"[:sort {levelEDN level}]\"\n"
   "  | .const name levels =>\n"
   "      s!\"[:const {quoteString name.toString} [{String.intercalate \" \" (levels.map levelEDN)}]]\"\n"
   "  | .app function argument => s!\"[:app {exprEDN function} {exprEDN argument}]\"\n"
   "  | .lam _ type body binder =>\n"
   "      s!\"[:lam {exprEDN type} {exprEDN body} {binderEDN binder}]\"\n"
   "  | .forallE _ type body binder =>\n"
   "      s!\"[:pi {exprEDN type} {exprEDN body} {binderEDN binder}]\"\n"
   "  | .letE _ type value body _ =>\n"
   "      s!\"[:let {exprEDN type} {exprEDN value} {exprEDN body}]\"\n"
   "  | .lit literal => s!\"[:unsupported :literal {quoteString (toString (repr literal))}]\"\n"
   "  | .mdata _ expression => exprEDN expression\n"
   "  | .mvar id => s!\"[:unsupported :mvar {quoteString (toString (repr id))}]\"\n"
   "  | .fvar id => s!\"[:unsupported :fvar {quoteString (toString (repr id))}]\"\n"
   "  | .proj typeName index structExpr =>\n"
   "      s!\"[:unsupported :projection {quoteString typeName.toString} {index} {exprEDN structExpr}]\"\n\n"
   "private def kindEDN : ConstantInfo → String\n"
   "  | .axiomInfo _ => \":axiom\"\n"
   "  | .thmInfo _ => \":theorem\"\n"
   "  | .defnInfo _ => \":definition\"\n"
   "  | .opaqueInfo _ => \":definition\"\n"
   "  | .quotInfo _ => \":unsupported-quotient\"\n"
   "  | .inductInfo _ => \":unsupported-inductive\"\n"
   "  | .ctorInfo _ => \":unsupported-constructor\"\n"
   "  | .recInfo _ => \":unsupported-recursor\"\n\n"
   "private def declarationEDN (environment : Environment) (name : Name) : String :=\n"
   "  match environment.find? name with\n"
   "  | none => \"{\" ++ s!\":foreign/name {quoteString name.toString} :foreign/error :missing\" ++ \"}\"\n"
   "  | some info =>\n"
   "      let levels := info.levelParams.map (fun level => quoteString level.toString)\n"
   "      let value := match info.value? true with | some body => exprEDN body | none => \"nil\"\n"
   "      \"{\" ++ s!\":foreign/name {quoteString name.toString} :foreign/kind {kindEDN info} \" ++\n"
   "      s!\":foreign/universes [{String.intercalate \" \" levels}] \" ++\n"
   "      s!\":foreign/type {exprEDN info.type} :foreign/value {value} \" ++\n"
   "      s!\":foreign/unsafe? {if info.isUnsafe then \"true\" else \"false\"}\" ++ \"}\"\n\n"))

(defn- lean-string [value]
  (str "\"" (-> value
                 (string/replace "\\" "\\\\")
                 (string/replace "\"" "\\\"")
                 (string/replace "\n" "\\n")) "\""))

(defn- proposition? [rainbow-environment declaration]
  (let [inferred (kernel/infer rainbow-environment
                               (:rainbow/type declaration)
                               (set (:rainbow/universes declaration)))]
    (when-not (= :checked (:status inferred))
      (reject! :lean-export/declaration-no-longer-checks
               "Checked declaration type could not be inferred during export"
               {:cause inferred :rainbow/id (:rainbow/id declaration)}))
    (= [:sort [:zero]]
       (:term (kernel/normalize rainbow-environment (:type inferred))))))

(defn export-source
  "Renders a checked declaration plus a structural Lean Expr exporter.

  Returns {:status :exported :source ...} or a categorized rejection.  The
  resulting Lean file writes the neutral fixture to :output-path only after
  Lean has accepted the theorem/definition body."
  [rainbow-environment id-or-alias
   {:keys [lean-namespace lean-name output-path]
    :or {lean-namespace "RainbowRoundTrip"
         lean-name "exportedDeclaration"}}]
  (try
    (let [declaration (checked-declaration rainbow-environment id-or-alias)
          kind (:rainbow/kind declaration)
          _ (when-not (contains? #{:theorem :definition} kind)
              (reject! :lean-export/unsupported-declaration-kind
                       "Only proved theorems and definitions can round-trip"
                       {:kind kind}))
          _ (when-not (:rainbow/value declaration)
              (reject! :lean-export/missing-value
                       "Exported declaration has no proof or definition body" {}))
          namespace-name (validate-qualified! :lean-export/unsafe-namespace
                                               lean-namespace [:lean-namespace])
          declaration-name (validate-identifier! :lean-export/unsafe-name
                                                  lean-name [:lean-name])
          _ (when-not (and (string? output-path) (not (string/blank? output-path)))
              (reject! :lean-export/invalid-output-path
                       "A non-empty neutral fixture output path is required"
                       {:output-path output-path}))
          universes (vec (:rainbow/universes declaration))
          _ (when-not (= (count universes) (count (set universes)))
              (reject! :lean-export/duplicate-universe
                       "Declaration universe parameters must be unique"
                       {:universes universes}))
          universe-set (set universes)
          universe-source (when (seq universes)
                            (str ".{" (string/join ", "
                                                   (map #(validate-identifier!
                                                          :lean-export/unsafe-universe-name
                                                          % [:rainbow/universes])
                                                        universes)) "}"))
          constants (native-lean-constants rainbow-environment)
          type-source (render-expression (:rainbow/type declaration) [] universe-set
                                         constants [:rainbow/type])
          value-source (render-expression (:rainbow/value declaration) [] universe-set
                                          constants [:rainbow/value])
          qualified-name (str namespace-name "." declaration-name)
          lean-kind (if (and (= :theorem kind)
                             (proposition? rainbow-environment declaration))
                      :theorem
                      :definition)
          declaration-keyword (if (= :theorem lean-kind) "theorem" "def")
          source
          (str "import Lean\n\n"
               "open Lean Elab Command\n\n"
               "namespace " namespace-name "\n\n"
               declaration-keyword " " declaration-name universe-source " :\n"
               "  " type-source " :=\n"
               "  " value-source "\n\n"
               neutral-exporter-source
               "run_cmd do\n"
               "  let environment ← getEnv\n"
               "  let declaration := declarationEDN environment `" qualified-name "\n"
               "  let output :=\n"
               "    \"{:foreign/schema-version 1 :foreign/system :lean \" ++\n"
               "    \":foreign/version \\\"" lean/pinned-version "\\\" \" ++\n"
               "    \":foreign/commit \\\"" lean/pinned-commit "\\\" \" ++\n"
               "    s!\":foreign/declarations [{declaration}]}\\n\"\n"
               "  IO.FS.writeFile " (lean-string output-path) " output\n\n"
               "end " namespace-name "\n")]
      {:status :exported
       :source source
       :rainbow/declaration-id (:rainbow/id declaration)
       :lean/name qualified-name
       :lean/kind lean-kind
       :kind-adaptation (when (not= kind lean-kind)
                          {:rainbow kind :lean lean-kind
                           :reason :lean-theorems-require-propositions})
       :output-path output-path
       :constructors #{:sort :bound :const :app :pi :lam :let}})
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected
       :error (ex-data exception)
       :message (ex-message exception)})))
