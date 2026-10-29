(ns rainbow.foreign.lean-export
  "Untrusted structural export of checked Rainbow declarations to pinned Lean.

  The exporter never establishes truth: it only renders a declaration already
  accepted by Rainbow.  Lean checks the rendered term, serializes its own Expr,
  and the ordinary foreign importer checks that expression again on return."
  (:require [clojure.string :as string]
            [rainbow.environment :as environment]
            [rainbow.foreign.lean :as lean]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]))

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

(defn- universe-name
  "Lean accepts any universe name written inside «»; only the guillemets themselves, whitespace and
  control characters are unsafe there. ASCII identifiers are left bare so recorded sources are stable."
  [value path]
  (let [rendered (str value)]
    (cond (re-matches lean-identifier-pattern rendered) rendered
          (re-matches #"[^«»\s\p{Cntrl}]+" rendered) (str "«" rendered "»")
          :else (reject! :lean-export/unsafe-universe-name "Value is not a safe Lean identifier"
                         {:path path :value value}))))

(defn- universe-list [universes]
  (when (seq universes)
    (str ".{" (string/join ", " (map #(universe-name % [:rainbow/universes]) universes)) "}")))

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
             (universe-name name path))
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

(defn- plain?
  "A variable of this type needs no @: its type has no implicit binder and no constant to unfold into one."
  [type]
  (not-any? #{:implicit :const} (tree-seq vector? seq type)))

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
             (let [[name plain?] (nth context index)] (str (when-not plain? "@") name)))
    :nat (let [n (second expression)]
           (when-not (and (integer? n) (<= 0 n))
             (reject! :lean-export/malformed-expression "Malformed natural-number literal"
                      {:path path :expression expression}))
           (str "(" n " : Nat)"))
    :const (let [id (second expression)
                 entry (get constants id)
                 levels (nth expression 2 nil)]
             (when-not entry
               (reject! :lean-export/unmapped-constant
                        "Rainbow constant has no explicit Lean mapping"
                        {:path (conj path 1) :rainbow/id id}))
             (when-not (vector? levels)
               (reject! :lean-export/malformed-constant
                        "Constant universe instantiation must be a vector"
                        {:path (conj path 2) :levels levels}))
             ;; an entry is a Lean name, {:name :levels fn}, or a fn of the levels giving [name levels] (copies)
             (let [[lean-name levels] (cond (fn? entry) (entry levels)
                                            (map? entry) [(:name entry) ((:levels entry) levels)]
                                            :else [entry levels])]
              (str "@" lean-name
                  (when-some [levels (seq levels)]
                    (str ".{" (string/join ", "
                                           (map-indexed
                                            (fn [index level]
                                              (render-level level universes
                                                            (conj path 2 index)))
                                            levels)) "}")))))
    :app (let [render #(render-expression %1 context universes constants %2)
               spine (loop [node expression arguments ()]
                       (if (= :app (first node)) (recur (second node) (cons (nth node 2 nil) arguments))
                           (cons node arguments)))
               head (render (first spine) (into path (repeat (dec (count spine)) 1)))]
           ;; A head rendered with @ (a constant, or a bound variable whose type may have implicit
           ;; binders) takes every argument Rainbow supplies, implicit ones included.
           (if (string/starts-with? head "@")
             (str "(" head " " (string/join " " (map-indexed #(render %2 (conj (into path (repeat (- (count spine) 2 %1) 1)) 2)) (rest spine))) ")")
             (str "(" (render (second expression) (conj path 1)) " "
                  (render (nth expression 2 nil) (conj path 2)) ")")))
    (:pi :lam)
    (let [tag (first expression)
          mode (nth expression 3 nil)
          name (str "x" (count context))
          domain (render-expression (second expression) context universes constants
                                    (conj path 1))
          body (render-expression (nth expression 2 nil) (into [[name (plain? (second expression))]] context)
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
               body (render-expression (nth expression 3 nil) (into [[name (plain? (second expression))]] context)
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
  resulting Lean file writes the neutral fixture to :output-path whenever its
  run_cmd runs, and Lean runs it even after rejecting the declaration (which it
  then adds with sorryAx).  A fixture is therefore no evidence by itself: a
  check must require Lean's zero exit status and the absence of sorryAx
  (rainbow.history.lean-round-trip/check-with-lean and the importer both do)."
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
          universe-source (universe-list universes)
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

;; ---- dependency closures: inductive blocks, logical principles, definitions, theorems --------------
;; Lean proofs, from Lean's axioms, of the translated statements of Rainbow's profile principles
;; (rainbow.math.profile). Rainbow's connectives are impredicative definitions that Lean unfolds; Lean
;; checks each proof, and #print axioms reports what it really uses.
(def principle-proofs
  {'logic/proof-irrelevance ["theorem" "by intro c l r P h; exact h"]
   'logic/function-extensionality
   ["theorem" "by intro A B f g h P hf; exact @Eq.subst _ P f g (funext fun x => h x (fun y => f x = y) rfl) hf"]
   'logic/proposition-extensionality
   ["theorem" "by intro l r h P hp; exact @Eq.subst Prop P l r (propext (h (l ↔ r) fun a b => Iff.intro a b)) hp"]
   'logic/excluded-middle
   ["theorem" "by intro P R hl hr; exact (Classical.em P).elim hl fun hn => hr fun p => absurd p hn"]
   'logic/choice ["noncomputable def" "fun A P e => Classical.choice (e (Nonempty A) fun x _ => Nonempty.intro x)"]})

(defn- lean-word [declaration]
  (let [x (string/replace (str (first (sort (map str (:rainbow/aliases declaration))))) #"[^A-Za-z0-9_]+" "_")]
    (if (re-matches #"[A-Za-z].*" x) x (str "d" x))))

(defn- unit-name [declaration]
  (str (lean-word declaration) "_" (subs (:rainbow/id declaration) 7 15)))

(defn- never-zero? [level]
  (case (first level)
    :succ true
    :max (or (never-zero? (second level)) (never-zero? (nth level 2)))
    :imax (never-zero? (nth level 2))
    false))

;; ---- universe splitting: Lean copies of Rainbow's universe-polymorphic units ----------------------
;; Rainbow admits a type at Sort u (List, Option) or Sort (max u v) (Sum, Product), a Prop for u = 0 only;
;; Lean refuses such a type. Each unit is therefore exported as copies: whenever rendering a copy meets a
;; level that is neither surely 0 nor surely a successor where a copy must be chosen (a block's sort, or
;; the universe argument of a use of a split unit), the copy is replaced by two, with the first exposed
;; universe parameter p := 0 and p := p + 1 (p keeps its name and stands for one less). Together they
;; cover every value. A copy violating a level requirement of Rainbow's (:rainbow/level-requirements,
;; levels that must be >= 1) is dropped, since Rainbow admits no such instance. A copy is named
;; <unit>_U<code>, one letter per universe parameter: 0, s (successor) or x (not split).
(defn- split! [level] (throw (ex-info "Level must be split" {::split (term/normalize-level level)})))

(defn- level-pred [level]
  (let [level (term/normalize-level level)] (when (= :succ (first level)) (second level))))

(defn- exposed-params [level]
  (case (first level)
    :param #{(second level)}
    (:max :imax) (into (exposed-params (second level)) (exposed-params (nth level 2)))
    #{}))

(defn- copy-suffix [universes sigma]
  (when (seq sigma) (apply str "_U" (map #(case (first (sigma %)) nil "x" :zero "0" "s") universes))))

(defn- at-copy [term sigma] (if (seq sigma) (term/instantiate-universes term sigma) term))

(defn- split-copies [universes requirements render]
  (letfn [(copies [sigma]
            (if (some #(= [:zero] (term/instantiate-level % sigma)) requirements)
              [{:dropped sigma}]
              (try [(render sigma)]
                   (catch clojure.lang.ExceptionInfo exception
                     (let [p (some (exposed-params (::split (ex-data exception) [:zero])) universes)]
                       (when (or (nil? p) (contains? sigma p)) (throw exception))
                       (into (copies (assoc sigma p [:zero])) (copies (assoc sigma p [:succ [:param p]]))))))))]
    (copies {})))

(defn- pick-copy
  "The copy covering a use at these levels, and its universe arguments (a level p + 1 passes p)."
  [universes copies levels]
  (let [unsplit (volatile! nil)
        fit (fn [sigma]
              (loop [[p & ps :as all] universes [level & more] levels out []]
                (if (empty? all)
                  out
                  (let [cut (first (sigma p))
                        found (when cut (cond (= [:zero] (term/normalize-level level)) :zero (level-pred level) :succ))]
                    (cond (nil? cut) (recur ps more (conj out level))
                          (nil? found) (do (vreset! unsplit level) nil)
                          (= cut found) (recur ps more (cond-> out (= :succ cut) (conj (level-pred level))))
                          :else nil)))))]
    (or (some #(let [out (fit (:sigma %))] (when (vector? out) [% out])) copies)
        (if-let [level @unsplit]
          (split! level)
          (reject! :lean-export/no-copy "No exported copy covers this use" {:levels levels})))))

(defn- block-members [rainbow-environment block]
  (let [[inductive & members] (map #(environment/declaration rainbow-environment %) (:block/member-ids block))]
    [inductive (butlast members) (last members)]))

(defn- block-constants
  "Rainbow's block constants, each use mapped to its copy. Lean's T.rec takes the motive universe first,
  and none when the copy eliminates only into Prop."
  [[inductive constructors recursor] copies]
  (let [universes (:rainbow/universes inductive)
        pick #(pick-copy universes copies %)]
    (into {(:rainbow/id inductive) #(let [[copy levels] (pick %)] [(:name copy) levels])
           (:rainbow/id recursor)
           (fn [levels]
             (let [[copy out] (pick (pop levels))]
               (when (and (:restricted? copy) (not= [:zero] (term/normalize-level (peek levels))))
                 (reject! :lean-export/large-elimination-differs "Lean eliminates this type only into Prop"
                          {:rainbow/id (:rainbow/id recursor) :levels levels}))
               [(str (:name copy) ".rec") (cond->> out (not (:restricted? copy)) (cons (peek levels)))]))}
          (map-indexed (fn [i constructor]
                         [(:rainbow/id constructor)
                          #(let [[copy levels] (pick %)] [(nth (:constructor-names copy) i) levels])])
                       constructors))))

(defn- telescope
  "Renders the first n binders of a Pi type as Lean binders: [binders context remaining-body]."
  [type n universes constants]
  (loop [type type context [] binders []]
    (if (= (count binders) n)
      [binders context type]
      (let [name (str "x" (count context))
            domain (render-expression (second type) context universes constants [:telescope])]
        (recur (nth type 2) (into [[name (plain? (second type))]] context)
               (conj binders (str "(" name " : " domain ")")))))))

(defn- block-copy
  "One copy of a Rainbow block as a Lean inductive (Nat stays Lean's Nat), then definitions asserting that
  Lean's type, constructors and recursor have Rainbow's translated types at the copy's levels. A Prop block
  eliminates only into Prop when it has two or more constructors, in both systems (Rainbow's Prop blocks
  have only Prop fields); Lean decides that itself, and the recursor assertion checks that they agree."
  [[inductive constructors recursor :as members] block namespace-name constants sigma]
  (let [universes (vec (:rainbow/universes inductive))
        us (vec (remove #(= [:zero] (sigma %)) universes))
        motive kernel/motive-universe-parameter
        sort-level (term/instantiate-level (get-in block [:block/spec :block/sort-level]) sigma)
        prop? (= [:zero] sort-level)
        _ (when-not (or prop? (never-zero? sort-level)) (split! sort-level))
        native (get constants (:rainbow/id inductive))
        local (str (unit-name inductive) (copy-suffix universes sigma))
        name (or native (str namespace-name "." local))
        copy {:sigma sigma :name name :restricted? (and prop? (< 1 (count constructors)))
              :constructor-names (mapv #(or (get constants (:rainbow/id %)) (str name "." (lean-word %))) constructors)}
        mapped (into constants (block-constants members [copy]))
        levels (mapv #(term/instantiate-level [:param %] sigma) universes)
        check (fn [suffix id type us levels]
                (str "noncomputable def " local ".rainbowCheck" suffix (universe-list us) " :\n  "
                     (render-expression type [] (set us) mapped [:check]) " :=\n  "
                     (render-expression [:const id levels] [] (set us) mapped [:check])))
        own (assoc constants (:rainbow/id inductive) {:name local :levels (constantly nil)})
        parameter-count (get-in recursor [:rainbow/recursor :parameter-count])
        [binders context result] (telescope (at-copy (:rainbow/type inductive) sigma) parameter-count (set us) own)]
    (when (and native (some nil? (map #(get constants (:rainbow/id %)) constructors)))
      (reject! :lean-export/unmapped-constant "Native Lean type has an unmapped constructor"
               {:rainbow/id (:rainbow/id inductive)}))
    {:copy copy
     :chunks
     (concat
      (when-not native
        [(str "inductive " local (universe-list us) " " (string/join " " binders) " : "
              (render-expression result context (set us) own [:sort-level]) " where"
              (apply str (for [[declaration constructor-name] (map vector constructors (:constructor-names copy))
                               :let [[_ context fields] (telescope (at-copy (:rainbow/type declaration) sigma)
                                                                   parameter-count (set us) own)]]
                           (str "\n  | " (subs constructor-name (inc (count name))) " : "
                                (render-expression fields context (set us) own [:constructor])))))])
      [(check "Type" (:rainbow/id inductive) (at-copy (:rainbow/type inductive) sigma) us levels)]
      (map-indexed #(check (str "Ctor" %1) (:rainbow/id %2) (at-copy (:rainbow/type %2) sigma) us levels) constructors)
      [(if (:restricted? copy)
         (check "Rec" (:rainbow/id recursor) (term/instantiate-universes (:rainbow/type recursor) (assoc sigma motive [:zero]))
                us (conj levels [:zero]))
         (check "Rec" (:rainbow/id recursor) (at-copy (:rainbow/type recursor) sigma) (conj us motive)
                (conj levels [:param motive])))])
     :report {:alias (first (:rainbow/aliases inductive)) :lean/name name :native? (boolean native)
              :prop? prop? :prop-only-elimination? (:restricted? copy) :copy (copy-suffix universes sigma)}}))

(defn- declaration-copy [rainbow-environment declaration namespace-name constants sigma]
  (let [kind (:rainbow/kind declaration)
        universes (vec (:rainbow/universes declaration))
        local (str (unit-name declaration) (copy-suffix universes sigma))
        render #(render-expression (at-copy % sigma) [] (set (remove (comp #{[:zero]} sigma) universes)) constants [%2])
        [keyword proof] (cond (= :axiom kind) (or (some principle-proofs (:rainbow/aliases declaration)) ["axiom"])
                              (and (= :theorem kind) (proposition? rainbow-environment declaration)) ["theorem"]
                              :else ["noncomputable def"])
        value (or proof (some-> (:rainbow/value declaration) (render :rainbow/value)))]
    {:copy {:sigma sigma :name (str namespace-name "." local)}
     :chunks [(str keyword " " local (universe-list (remove (comp #{[:zero]} sigma) universes)) " :\n  "
                   (render (:rainbow/type declaration) :rainbow/type) (when value (str " :=\n  " value)))]
     :report {:kind kind :lean/keyword keyword :lean/name (str namespace-name "." local)
              :alias (first (:rainbow/aliases declaration)) :copy (copy-suffix universes sigma)}}))

(defn export-closure
  "Renders a checked declaration and its whole dependency closure as one Lean file in dependency order:
  inductive blocks (block-copy), profile principles as Lean theorems proved from Lean's axioms
  (principle-proofs; any other axiom stays a Lean axiom), definitions and theorems, each as the copies
  split-copies makes, then #print axioms for every copy of the target. :units reports each copy, and
  :dropped-copies those Rainbow's level requirements exclude. :cache (an atom) shares rendered units
  across calls."
  [rainbow-environment id-or-alias {:keys [lean-namespace cache] :or {lean-namespace "RainbowXcheck"}}]
  (try
    (let [namespace-name (validate-qualified! :lean-export/unsafe-namespace lean-namespace [:lean-namespace])
          target (checked-declaration rainbow-environment id-or-alias)
          cache (or cache (atom {}))
          declaration #(or (environment/declaration rainbow-environment %)
                           (reject! :lean-export/unknown-declaration "Closure names a missing declaration"
                                    {:declaration %}))
          unit-of #(or (:rainbow/block-id %) (:rainbow/id %))
          members #(or (:block/member-ids (environment/block rainbow-environment %)) [%])
          dependencies (fn [unit]
                         (->> (members unit) (map declaration)
                              (mapcat #(concat (term/constants (:rainbow/type %))
                                               (some-> (:rainbow/value %) term/constants)))
                              (remove (set (members unit))) distinct sort (map (comp unit-of declaration)) distinct))
          order (let [seen (atom #{}) order (atom [])]
                  (letfn [(visit [unit]
                            (when-not (@seen unit)
                              (swap! seen conj unit)
                              (run! visit (dependencies unit))
                              (swap! order conj unit)))]
                    (visit (unit-of target))
                    @order))
          render (fn [constants unit]
                   (let [block (environment/block rainbow-environment unit)
                         parts (when block (block-members rainbow-environment block))
                         head (if block (first parts) (checked-declaration rainbow-environment unit))
                         copies (split-copies (vec (:rainbow/universes head))
                                              (mapcat #(:rainbow/level-requirements (declaration %)) (members unit))
                                              #(if block
                                                 (block-copy parts block namespace-name constants %)
                                                 (declaration-copy rainbow-environment head namespace-name constants %)))
                         kept (map :copy (remove :dropped copies))]
                     {:constants (if block
                                   (block-constants parts kept)
                                   {(:rainbow/id head) #(let [[copy levels] (pick-copy (:rainbow/universes head) kept %)]
                                                          [(:name copy) levels])})
                      :chunks (mapcat :chunks copies) :units (vec (keep :report copies))
                      :dropped (vec (for [c copies :when (:dropped c)]
                                      {:alias (first (:rainbow/aliases head)) :copy (copy-suffix (:rainbow/universes head) (:dropped c))}))}))
          {:keys [chunks units dropped last-units]}
          (reduce (fn [acc unit]
                    (let [r (or (get @cache unit) ((swap! cache assoc unit (render (:constants acc) unit)) unit))]
                      (-> acc (update :constants merge (:constants r)) (update :chunks into (:chunks r))
                          (update :units into (:units r)) (update :dropped into (:dropped r))
                          (assoc :last-units (:units r)))))
                  {:constants (native-lean-constants rainbow-environment) :chunks [] :units [] :dropped []} order)]
      {:status :exported
       :source (str "namespace " namespace-name "\n\n" (string/join "\n\n" chunks) "\n\nend " namespace-name
                    "\n\n" (apply str (map #(str "#print axioms " (:lean/name %) "\n") last-units)))
       :rainbow/declaration-id (:rainbow/id target)
       :lean/name (:lean/name (first last-units))
       :lean/names (mapv :lean/name last-units)
       :lean/keyword (:lean/keyword (first last-units))
       :units units
       :dropped-copies dropped})
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected :error (ex-data exception) :message (ex-message exception)})))
