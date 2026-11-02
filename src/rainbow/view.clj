(ns rainbow.view
  "Static views of checked data for auditors. `lein explore` writes the Proof Explorer: a directory
  with index.html and data.json (dependency graph, proof trees, axioms, kernel-computed example
  values), for a checkpoint or a proof bundle and a set of root theorems.

      lein explore <checkpoint.edn.gz | bundle.edn> [out-dir] [--roots a,b] [--modules ns,..]
                   [--lean results.edn] [--loop proofs.edn] [--loop-report report.edn] [--tree-cap n] [--offline]

  Exit code 0 when the page is written and every claim checks, 1 when a claim does not match its
  record or an input is refused (one `FAIL explore <what> -- <why> -- <what to check>` line, and
  nothing is written), 2 on a usage error.

  Nothing here is trusted. Every declaration shown was added by the kernel (checkpoint replay,
  module install, bundle replay or kernel/add-declaration of a loop proof); every statement is
  printed by rainbow.render from the kernel term; every example value is computed by
  kernel/normalize. The page is static: its data is inline (it opens from disk), the graph
  libraries come from pinned CDN URLs with integrity hashes, or with --offline are inlined from
  the vendored copies (MIT, see scripts/view-vendor-LICENSES.txt)."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as string]
            [rainbow.canonical :as canonical]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.render :as render]
            [rainbow.term :as term]))

;; ---------------------------------------------------------------- JSON and pages

(defn- json-string [s]
  (str "\"" (string/replace (str s) (re-pattern "[\\\\\"<>&\\x00-\\x1f\\x{2028}\\x{2029}]")
                            #(case % "\\" "\\\\" "\"" "\\\"" "\n" "\\n" "\t" "\\t"
                                   (format "\\u%04x" (int (first %))))) "\""))

(defn json
  "JSON text (nil map values left out; ratios as text such as \"3/2\"). <, > and & are escaped, so
  the text can sit inside an HTML script element."
  [x]
  (cond (nil? x) "null" (boolean? x) (str x)
        (ratio? x) (json-string x)
        (integer? x) (str x)
        (number? x) (str (double x))
        (keyword? x) (json-string (subs (str x) 1))
        (map? x) (str "{" (string/join "," (for [[k v] x :when (some? v)]
                                             (str (json-string (if (keyword? k) (name k) k)) ":" (json v)))) "}")
        (coll? x) (str "[" (string/join "," (map json x)) "]")
        :else (json-string x)))

(def vendored
  "The pinned CDN scripts the pages load and the vendored copies --offline inlines (same bytes)."
  {"https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.28.1/cytoscape.min.js" "scripts/cytoscape-3.28.1.min.js"
   "https://cdnjs.cloudflare.com/ajax/libs/dagre/0.8.5/dagre.min.js" "scripts/dagre-0.8.5.min.js"
   "https://cdn.jsdelivr.net/npm/cytoscape-dagre@2.5.0/cytoscape-dagre.js" "scripts/cytoscape-dagre-2.5.0.js"})

(defn page
  "The HTML of a template with `data` inline. With offline?, each pinned script is replaced by its
  vendored copy and web fonts are dropped (system fonts), so the page needs no network at all."
  [template data offline?]
  (let [html (string/replace template "/*RAINBOW-DATA*/" (json data))]
    (if-not offline?
      html
      (-> (reduce (fn [h [url path]]
                    (let [js (slurp path)]
                      (assert (not (re-find #"(?i)</script" js)) (str path " cannot be inlined"))
                      (string/replace h (re-pattern (str "<script src=\"" (java.util.regex.Pattern/quote url) "\"[^>]*></script>"))
                                      (string/re-quote-replacement (str "<script>" js "</script>")))))
                  html vendored)
          (string/replace #"<link [^>]*fonts\.(googleapis|gstatic)\.com[^>]*>\n?" "")))))

(defn write-page!
  "Writes dir/index.html and dir/<json-name>; returns the directory."
  [dir template-path json-name data offline?]
  (.mkdirs (io/file dir))
  (spit (io/file dir json-name) (json data))
  (spit (io/file dir "index.html") (page (slurp template-path) data offline?))
  dir)

;; ---------------------------------------------------------------- what to show

(defn- refuse!
  "Throws a refusal that lein explore prints as one line, `FAIL explore <what> -- <why> -- <check>`:
  why is the message; what failed defaults to the source file; check says what to do next."
  ([why] (refuse! why nil nil))
  ([why what check]
   (throw (ex-info why (cond-> {:error/category :view/refused}
                         what (assoc :explore/what what)
                         check (assoc :explore/check check))))))

(defn- reason
  "A throwable's message, with its cause's when that says more (a compile error wraps the real one)."
  [^Throwable e]
  (let [m (or (.getMessage e) (.getName (class e)))
        c (some-> (.getCause e) .getMessage)]
    (if (and c (not (string/includes? m c))) (str m ": " c) m)))

(defn install-modules
  "Installs each module (a namespace with extend-environment) in order, as bundles record them.
  Refuses, naming the module, when it cannot be loaded or is not a proof module."
  [env modules]
  (reduce (fn [env m]
            (let [s (symbol (str m)) what (str "module " m)]
              (try (require s)
                   (catch Exception e
                     (refuse! (str "could not be loaded: " (reason e)) what
                              (str "Check the namespace name (such as rainbow.math.finite.rational-argmax, not a file "
                                   "path), and run explore from the Rainbow directory so that its source is on the classpath."))))
              (if-let [extend (ns-resolve s 'extend-environment)]
                (extend env)
                (refuse! "not a proof module: it defines no extend-environment" what
                         "Name the proof module that installs the declarations, as lein verify takes it."))))
          env modules))

(defn- replayed
  "The environment of the checkpoint at path, replayed by the kernel; refuses with the replay's reason."
  ([path] (replayed path (str "checkpoint " path)))
  ([path what]
   (let [r (checkpoint/load-checkpoint path)]
     (when-not (= :replayed (:status r))
       (let [category (:error/category r)]
         (if (and (keyword? category) (= "checkpoint-read-failed" (name category)))
           (refuse! (str "could not be read: " (:message r)) what
                    (str "Check that the checkpoint exists and is complete; checkpoint paths such as artifacts/... are "
                         "relative to the Rainbow directory, so run explore from there."))
           (refuse! (str "did not replay (" (pr-str (or category (:status r))) ")" (some->> (:message r) (str ": "))) what
                    "Use a checkpoint written by this version of Rainbow; lein verify --checkpoint <path> <module> shows the same replay."))))
     (:environment r))))

(defn- read-file [path]
  (let [data (java.nio.file.Files/readAllBytes (.toPath (io/file path)))
        unpack (try (requiring-resolve 'rainbow.bundle.binary/unpack) (catch Exception _ nil))]
    (if (and unpack ((requiring-resolve 'rainbow.bundle.binary/binary?) data))
      (unpack data)
      (edn/read-string {:default tagged-literal} (String. ^bytes data "UTF-8")))))

(def ^:private bundle-schemas "The proof bundle schema versions explore replays." #{1 2 3})

(def ^:private source-check
  (str "explore takes a checkpoint (.edn.gz) or a proof bundle (.edn, or the binary file share-bundle --binary "
       "writes); lein verify --bundle <file> checks a bundle on its own."))

(defn- read-source
  "The value in a source file that is not gzipped (a bundle, or a plain checkpoint); refuses, naming
  the file, when it is missing, a directory or not readable."
  [path]
  (let [f (io/file (str path))]
    (cond (not (.exists f)) (refuse! "no such file" (str path) (str "Check the path. " source-check))
          (.isDirectory f) (refuse! "is a directory, not a file" (str path) (str "Name the file. " source-check)))
    (when-not (string/ends-with? (str path) ".gz")
      (try (read-file path)
           (catch Exception e
             (refuse! (str "not readable: " (reason e)) (str path)
                      (str "Check that the file is complete (a copy cut short ends in the middle of a form). " source-check)))))))

(defn- replay-bundle
  "The bundle's base (checkpoint and modules, to the recorded environment and names ids), then every
  entry through kernel/add-declaration or kernel/add-inductive-block. Refuses on any mismatch."
  [bundle]
  (let [bundle (if (= 3 (:rainbow.bundle/schema-version bundle))
                 (try ((requiring-resolve 'rainbow.bundle.shared/decode) bundle)
                      (catch Exception e
                        (refuse! (str "the shared encoding could not be decoded: " (reason e)) nil
                                 "Check that the bundle is complete; lein verify --bundle <file> reports the same.")))
                 bundle)
        {:keys [checkpoint modules environment-id names-id]} (:base bundle)
        base (install-modules (replayed checkpoint (str "the bundle's base checkpoint " checkpoint)) modules)
        verify "lein verify --bundle <file> checks the bundle and says which part does not match."]
    (when-not (= environment-id (environment/environment-id base))
      (refuse! "the bundle's base modules did not reproduce its environment id" nil
               (str "The bundle was made on other versions of its base modules. " verify)))
    (when (and names-id (not= names-id (persistence/names-id base)))
      (refuse! "the bundle's base names do not match its names id" nil (str "The bundle was made on other base names. " verify)))
    (binding [kernel/*reduction-budget* (max kernel/*reduction-budget* (get-in bundle [:check :reductions] 0))]
      {:base-env base :checkpoint checkpoint :modules modules
       :env (reduce (fn [env {:entry/keys [kind value]}]
                      (let [r (if (= :inductive-block kind) (kernel/add-inductive-block env value) (kernel/add-declaration env value))]
                        (if (= :accepted (:status r)) (:environment r)
                            (refuse! (str "the kernel rejected bundle entry " (or (:rainbow/id value) (:rainbow/aliases value)))
                                     nil (str "The bundle does not check. " verify)))))
                    base (or (:entries bundle) (for [d (:declarations bundle)] {:entry/kind :declaration :entry/value d})))
       :claims (:claims bundle)})))

(defn- install-loop-proofs
  "Proofs from a proving-loop record [{:alias :how :proved {:type :proof}}], each added by the kernel
  unless the environment already has that alias."
  [env entries]
  (reduce (fn [env {:keys [alias proved]}]
            (if (environment/resolve-id env alias) env
                (let [{:keys [type proof]} proved
                      r (kernel/add-declaration env {:rainbow/kind :theorem :rainbow/aliases #{alias} :rainbow/universes []
                                                     :rainbow/type type :rainbow/value proof :rainbow/transparency :opaque
                                                     :rainbow/dependencies (into (term/constants type) (term/constants proof))
                                                     :rainbow/provenance {:origin :native :producer :proving-loop}
                                                     :rainbow/schema-version 1})]
                  (if (= :accepted (:status r)) (:environment r)
                      (refuse! (str "the kernel rejected loop proof " alias) "--loop"
                               "Check that the --loop file is the proving loop's record for this checkpoint and modules.")))))
          env entries))

(defn load-source
  "{:env :base-env :source :claims} for a checkpoint path (with modules installed) or a proof bundle.
  A file that is missing or unreadable, or holds neither a bundle nor a checkpoint, is refused."
  [path {:keys [modules loop]}]
  (let [value (read-source path)
        gz? (string/ends-with? (str path) ".gz")
        r (cond (and (map? value) (contains? value :rainbow.bundle/schema-version))
                (let [v (:rainbow.bundle/schema-version value)]
                  (when-not (bundle-schemas v)
                    (refuse! (str "a proof bundle of schema " (pr-str v) ", which this version does not read (it reads "
                                  (string/join ", " (sort bundle-schemas)) ")")
                             (str path) "Use the Rainbow release that wrote the bundle, or a newer one."))
                  (assoc (replay-bundle value) :kind "bundle"))
                (or gz? (and (map? value) (or (contains? value :rainbow.checkpoint/schema-version)
                                              (contains? value :rainbow.checkpoint/id))))
                (let [base (replayed path)] {:kind "checkpoint" :checkpoint path :modules modules :base-env base :env (install-modules base modules)})
                :else
                (refuse! (str "neither a proof bundle (no :rainbow.bundle/schema-version) nor a checkpoint (no :rainbow.checkpoint/id), but "
                              (cond (nil? value) "an empty file" (map? value) "a map without either key" :else (str "a " (.getSimpleName (class value)))))
                         (str path) (str "Check that this is the file you meant: " source-check)))]
    (assoc r :env (install-loop-proofs (:env r) loop)
           :source {:kind (:kind r) :path (str path) :checkpoint (str (:checkpoint r)) :modules (mapv str (:modules r))})))

;; ---------------------------------------------------------------- terms as text and as proof trees

(defn- spine [t] (loop [x t args ()] (if (= :app (first x)) (recur (second x) (cons (nth x 2) args)) [x (vec args)])))
(def ^:private infix {"algebra/nat-add" "+" "nat/multiply" "×" "nat/distance" "dist" "nnrat/add" "+" "nnrat/multiply" "×"
                      "nnrat/divide" "÷" "nnrat/equivalent" "≈"})
(def ^:private letters "xyzwuvabcdefghjkmnpqrst")
(defn- fresh [names base] (let [taken (set names)] (loop [c base] (if (taken c) (recur (str c "′")) c))))
(defn- binder-name [names] (let [d (count names)] (fresh names (str (nth letters (mod d 23)) (when (>= d 23) (quot d 23))))))
(defn- uses-bound? [t k]
  (case (first t)
    :bound (= k (second t))
    :app (or (uses-bound? (nth t 1) k) (uses-bound? (nth t 2) k))
    (:lam :pi) (or (uses-bound? (nth t 1) k) (uses-bound? (nth t 2) (inc k)))
    :let (or (uses-bound? (nth t 1) k) (uses-bound? (nth t 2) k) (uses-bound? (nth t 3) (inc k)))
    false))
(defn- term-size [t] (case (first t) (:app :lam :pi) (+ 1 (term-size (nth t 1)) (term-size (nth t 2)))
                           :let (+ 1 (term-size (nth t 1)) (term-size (nth t 2)) (term-size (nth t 3))) 1))
(defn- truncate [s n] (if (> (count s) n) (str (subs s 0 (dec n)) "…") s))

(defn- context
  "Ids of the constants the views recognise in env (nil when env lacks them)."
  [env]
  (let [rid #(environment/resolve-id env %)]
    {:env env :alias (memoize (fn [id] (some-> (environment/declaration env id) :rainbow/aliases sort first str)))
     :nat [:const (rid 'data/Nat) []] :q [:const (rid 'nnrat/NonnegativeRational) []] :eq (rid 'equality/Eq)
     :qeq (rid 'nnrat/equivalent) :make (rid 'nnrat/make) :pair (rid 'data/pair) :zero [:const (rid 'data/zero) []]}))

(defn- nat-literal [c t] (cond (= :nat (first t)) (second t) (= (:zero c) t) 0))

(defn- show
  "Compact text for a core term under a list of binder names."
  [c t names]
  (case (first t)
    :sort (if (= [:zero] (second t)) "Prop"
              (str "Sort " ((fn level [l] (case (first l) :zero "0" :param (str (second l)) :succ (str (level (second l)) "+1")
                                                (str (name (first l)) " " (string/join " " (map level (rest l)))))) (second t))))
    :bound (or (nth names (second t) nil) (str "#" (second t)))
    :nat (str (second t))
    :const (or ((:alias c) (second t)) (subs (str (second t)) 0 14))
    :app (let [[h args] (spine t) hs (show c h names) op (infix hs)
               lits (when (and (= [:const (:make c) []] h) (= 2 (count args))) (map #(nat-literal c %) args))]
           (cond (and lits (every? some? lits)) (str (first lits) "/" (inc (second lits)))
                 (and (= hs "equality/Eq") (= 3 (count args))) (str (show c (nth args 1) names) " = " (show c (nth args 2) names))
                 (and op (= 2 (count args))) (str "(" (show c (first args) names) " " op " " (show c (second args) names) ")")
                 :else (str "(" hs " " (string/join " " (map #(show c % names) args)) ")")))
    :lam (let [n (binder-name names)] (str "fun " n " => " (show c (nth t 2) (cons n names))))
    :pi (let [dom (show c (second t) names) dom (if (#{:pi :lam} (first (second t))) (str "(" dom ")") dom)]
          (if (uses-bound? (nth t 2) 0)
            (let [n (binder-name names)] (str "∀ " n " : " dom ", " (show c (nth t 2) (cons n names))))
            (str dom " → " (show c (nth t 2) (cons "_" names)))))
    :let (let [n (binder-name names)] (str "let " n " := " (show c (nth t 2) names) " in " (show c (nth t 3) (cons n names))))
    (pr-str t)))

(defn- proof-tree
  "A navigable tree of a proof term: binders become 'assume', application spines 'use', recursors
  'induction'. `given` names the outermost binders. At most `budget` steps; every cut is a node
  counting the term nodes it hides."
  [c t names given budget shown]
  (if (neg? (swap! budget dec))
    (let [n (term-size t)] {:k "more" :label (str "… " n " term node" (when (not= 1 n) "s") " not shown") :hidden n
                            :explain (str "This part of the proof (" n " term nodes) is past the page's step limit.")})
    (let [sub #(proof-tree c %1 %2 %3 budget shown)]
      (swap! shown inc)
      (case (first t)
        :lam (let [n (if (seq given) (fresh names (first given)) (binder-name names))]
               {:k "assume" :label (str "assume " n " : " (truncate (show c (second t) names) 80))
                :explain (str "Introduce " n ". The rest of the proof may use it.") :children [(sub (nth t 2) (cons n names) (rest given))]})
        :let (let [n (binder-name names)]
               {:k "let" :label (str "let " n) :explain "A local definition used by the rest of the proof."
                :children [(sub (nth t 2) names nil) (sub (nth t 3) (cons n names) nil)]})
        :app (let [[h args] (spine t) hs (show c h names) rec? (string/ends-with? hs ".rec") const? (= :const (first h))]
               {:k (cond rec? "induction" const? "use" :else "apply")
                :label (truncate (str (if rec? "induction: " "use ") hs) 90)
                :ref (when (and const? (not rec?)) (second h))
                :explain (cond rec? (str "Proof by cases on a value of an inductive type, using its recursor " hs
                                         ": the motive (what is proved), one case per constructor, then the value.")
                               const? (str "Apply " hs " to " (count args) " argument(s).")
                               :else (str "Apply the assumption " hs " to " (count args) " argument(s)."))
                :children (mapv #(sub % names nil) args)})
        :const {:k "use" :label (str "use " (show c t names)) :ref (second t) :explain (str "Refer to " (show c t names) ", already checked.")}
        :bound {:k "var" :label (show c t names) :explain "An assumption or variable introduced above."}
        :nat {:k "num" :label (str (second t)) :explain "A natural-number literal."}
        :sort {:k "sort" :label (show c t names) :explain "A universe of types or propositions."}
        {:k "type" :label (truncate (show c t names) 90) :explain "A type or statement given as an argument."}))))

(defn- proof-binder-names
  "The statement's source binder names for the proof's outer lambdas, when those match the
  statement's ∀ binders one to one (same count, same domains); otherwise nil."
  [env d]
  (when-let [named (try (render/named-type env (first (sort (:rainbow/aliases d))) (:rainbow/type d)) (catch Throwable _ nil))]
    (let [binders (fn [t k] (loop [t t out []] (if (= k (first t)) (recur (nth t 2) (conj out t)) out)))
          pis (binders (:rainbow/type d) :pi) lams (take (count pis) (binders (:rainbow/value d) :lam))
          names (map #(get % 4) (binders named :pi))]
      (when (and (seq pis) (= (count pis) (count names) (count lams)) (= (map second pis) (map second lams)) (every? some? names))
        (mapv str names)))))

;; ---------------------------------------------------------------- example values, computed by the kernel

(def reduction-budget 200000)

(defn- equation
  "{:binders [:nat|:nnrat ..] :rel :eq-nat|:eq-q|:equiv-q :lhs :rhs} for a statement ∀ over ℕ / ℚ≥0
  of equality/Eq over ℕ or ℚ≥0 or of nnrat/equivalent; nil otherwise."
  [c t]
  (let [types (set [(:nat c) (:q c)])]
    (loop [t t binders []]
      (if (= :pi (first t))
        (when (types (second t)) (recur (nth t 2) (conj binders (if (= (:nat c) (second t)) :nat :nnrat))))
        (let [[h args] (spine t)]
          (when (and (seq binders) (= :const (first h)))
            (cond (and (= (:eq c) (second h)) (= 3 (count args)) (types (first args))
                       (or (= (:q c) (first args)) (every? #{:nat} binders)))
                  {:binders binders :rel (if (= (:q c) (first args)) :eq-q :eq-nat) :lhs (nth args 1) :rhs (nth args 2)}
                  (and (= (:qeq c) (second h)) (= 2 (count args))) {:binders binders :rel :equiv-q :lhs (first args) :rhs (second args)})))))))

(defn- value-of
  "{:nat n} or {:q {:n :d}} (a ℚ≥0 pair (n, d) means n/(d+1)) when the kernel normalizes t to one."
  [c t]
  (let [r (kernel/normalize (:env c) t {:rainbow.kernel/literals true :reductions reduction-budget})
        v (when (= :normalized (:status r)) (:term r))]
    (when v
      (if-let [n (nat-literal c v)]
        {:nat n}
        (let [[h args] (spine v) [n d] (map #(nat-literal c %) (drop 2 args))]
          (when (and (= [:const (:pair c) []] h) (= 4 (count args)) n d) {:q {:n n :d (inc d)}}))))))

(defn- examples [c d]
  (when-let [{:keys [binders rel lhs rhs]} (equation c (:rainbow/type d))]
    (let [r (java.util.Random. (hash (:rainbow/id d)))
          pick #(if (= % :nat) (.nextInt r 7) {:n (.nextInt r 7) :d (inc (.nextInt r 4))})
          q? (not= rel :eq-nat)
          q-term (fn [{:keys [n d]}] [:app [:app [:const (:make c) []] [:nat n]] [:nat (dec d)]])
          input? (fn [t] (let [[h args] (spine t)] (and (= [:const (:make c) []] h) (every? #(nat-literal c %) args))))
          subterms (fn subterms [t] (let [[h args] (spine t)]
                                      (concat (when (= :app (first t)) (mapcat subterms args))
                                              (when (and (= :app (first t)) (= :const (first h)) (not (#{(:eq c) (:qeq c)} (second h))) (not (input? t))) [t]))))
          value (fn [t] (let [v (value-of c t)] (if q? (:q v) (:nat v))))]
      (vec (for [vs (distinct (cons (mapv #(if (= % :nat) 2 {:n 1 :d 2}) binders) (repeatedly 4 #(mapv pick binders))))
                 :let [ts (reverse (map #(if (number? %) [:nat %] (q-term %)) vs))   ; the last binder is index 0
                       l (reduce term/instantiate lhs ts) rr (reduce term/instantiate rhs ts)
                       lv (value l) rv (value rr)]
                 :when (and lv rv)]
             {:type (if q? "nnrat" "nat") :rel (name rel) :inputs (mapv #(if (number? %) % (str (:n %) "/" (:d %))) vs)
              :lhs lv :rhs rv
              :equal (if (= rel :equiv-q) (= (*' (:n lv) (:d rv)) (*' (:n rv) (:d lv))) (= lv rv))
              :steps (vec (for [s (distinct (concat (subterms l) (subterms rr))) :let [v (value-of c s)] :when v]
                            (merge {:expr (show c s [])} (if (:nat v) {:value (:nat v)} {:q (:q v)}))))})))))

;; ---------------------------------------------------------------- the Proof Explorer's data

(defn- closure [env ids]
  (loop [todo (vec ids) seen #{}]
    (if-let [x (peek todo)]
      (recur (into (pop todo) (remove seen (:rainbow/dependencies (environment/declaration env x)))) (conj seen x))
      seen)))

(defn- how-class [s] (cond (string/includes? s "hand-written") "hand" (string/includes? s "AI proposal") "ai" :else "search"))

(defn- tour
  "Up to five stops, each caption computed from the node it names."
  [nodes]
  (let [roots (filter :root nodes) axiom? #(= :axiom (:kind %))
        pick (fn [pred] (first (filter pred roots)))]
    (vec (keep (fn [[n caption]] (when n {:id (:id n) :caption (caption n)}))
               [[(pick #(and (empty? (:axioms %)) (seq (:examples %))))
                 #(str (:alias %) " uses no axiom; pick an input row and run it step by step: every value is computed by the kernel ("
                       (count (:examples %)) " rows).")]
                [(pick #(and (= :theorem (:kind %)) (empty? (:axioms %)) (not (seq (:examples %)))))
                 #(str (:alias %) " uses no axiom. Its proof tree is below the statement; click a lemma to move to it.")]
                [(pick #(seq (:axioms %))) #(str (:alias %) " depends on the axiom(s) " (string/join ", " (:axioms %)) ", so it is amber.")]
                [(pick :how) #(str (:alias %) " was produced by the proving loop (" (:how %) "); the kernel re-checked it.")]
                [(pick :lean) #(str "Lean also accepted " (:alias %) "; Lean's #print axioms: "
                                    (or (not-empty (string/join ", " (:axioms (:lean %)))) "none") ".")]
                [(first (filter axiom? nodes)) #(str (:alias %) " is an axiom: assumed, not proved. Theorems that use it list it.")]]))))

(defn explorer-data
  "The Proof Explorer's data for roots (declaration ids; default every theorem). Options: :lean (rows
  of a Lean cross-check, {:id :verdict :lean-axioms :rainbow-axioms :units :split-units}), :loop
  (proving-loop records {:alias :how}), :loop-report (search telemetry {:results [{:goal-id ..}]}),
  :source and :base-env (provenance), :claims (a bundle's), :tree-cap (steps per proof tree)."
  [env {:keys [roots lean loop loop-report source base-env claims tree-cap] :or {tree-cap 600}}]
  (let [c (context env) decl #(environment/declaration env %)
        roots (vec (or (seq roots) (sort (for [[id d] (:rainbow.environment/declarations env) :when (= :theorem (:rainbow/kind d))] id))))
        ids (closure env roots) root? (set roots)
        lean-by-id (into {} (for [r lean :when (= :accepted (:verdict r))] [(:id r) r]))
        how-by-id (into {} (for [{:keys [alias how]} loop :let [id (environment/resolve-id env alias)] :when id] [id how]))
        telemetry (group-by :goal-id (:results loop-report))
        nodes (vec (for [id (sort-by (:alias c) ids)
                         :let [d (decl id) thm? (= :theorem (:rainbow/kind d)) proof? (and thm? (:rainbow/value d))
                               axioms (mapv (:alias c) (sort (kernel/axioms env id)))
                               st (try (render/statement env id) (catch Throwable e {:text (str "(statement not rendered: " (.getMessage e) ")")}))
                               given (when proof? (proof-binder-names env d))
                               budget (atom tree-cap) shown (atom 0)
                               proof (when proof? (proof-tree c (:rainbow/value d) [] given budget shown))
                               lean (lean-by-id id) how (how-by-id id)]]
                     (do (when lean (assert (= (set axioms) (set (:rainbow-axioms lean))) (str "Lean and Rainbow axiom sets disagree for " ((:alias c) id))))
                         {:id id :alias ((:alias c) id) :kind (:rainbow/kind d) :statement (:text st) :statementNames (some-> (:names st) name)
                          :axioms axioms :deps (vec (sort (filter ids (:rainbow/dependencies d)))) :root (contains? root? id)
                          :producer (some-> d :rainbow/provenance :producer str) :proof proof
                          :proofNames (when proof (if given "source" "generated"))
                          :size (when (:rainbow/value d) (term-size (:rainbow/value d))) :shown (when proof @shown)
                          :examples (when thm? (examples c d)) :how how :howClass (some-> how how-class)
                          :telemetry (when how (not-empty (vec (for [r (telemetry (canonical/content-id (:rainbow/type d)))]
                                                                 {:stage (name (:stage r)) :status (name (:status r)) :reason (some-> (:reason r) name)
                                                                  :states (:states r) :kernelChecks (:reported-kernel-checks r) :wallMs (:wall-ms r)
                                                                  :countsComplete (:counts-complete? r) :kernel (some-> (:kernel-status r) name)}))))
                          :lean (when lean {:axioms (vec (sort (:lean-axioms lean))) :units (:units lean) :splitUnits (:split-units lean)})})))]
    {:generated (str (java.time.Instant/now))
     :environment (environment/environment-id env)
     :baseEnvironment (some-> base-env environment/environment-id)
     :names (persistence/names-id env)
     :source source :treeCap tree-cap :reductions reduction-budget
     :lean (when (seq lean) {:accepted (count lean-by-id) :total (count lean)})
     :loop (when (seq loop) {:proofs (count how-by-id) :reportDate (:date loop-report)})
     :claims (not-empty (vec (for [[alias {:keys [id axioms]}] claims :let [rid (environment/resolve-id env alias)]]
                               {:alias (str alias) :id id :resolved rid :axioms (some->> rid (kernel/axioms env) sort (mapv (:alias c)))
                                :ok (and (= id rid) (= (set axioms) (some->> rid (kernel/axioms env) set)))})))
     :landing (first roots) :tour (tour nodes) :roots roots :nodes nodes}))

;; ---------------------------------------------------------------- command line

(defn parse-args
  "[positional ..] and {:flag value}; a flag in `switches` takes no value."
  [args switches]
  (loop [[a & more :as args] args pos [] opts {}]
    (cond (empty? args) [pos opts]
          (switches a) (recur more pos (assoc opts (keyword (subs a 2)) true))
          (string/starts-with? a "--") (recur (rest more) pos (assoc opts (keyword (subs a 2)) (first more)))
          :else (recur more (conj pos a) opts))))

(defn- csv [s] (when s (remove string/blank? (string/split s #","))))

(defn- read-edn
  "The EDN value in the file named by option flag (--lean, --loop, --loop-report), nil without the
  flag; refuses, naming the flag and file, when the file is missing or not readable EDN."
  [flag path]
  (when path
    (let [what (str "--" (name flag) " " path) f (io/file path)]
      (when-not (.isFile f)
        (refuse! (if (.exists f) "is a directory, not a file" "no such file") what (str "Check the path of the --" (name flag) " file.")))
      (try (edn/read-string {:default tagged-literal} (slurp f))
           (catch Exception e
             (refuse! (str "not readable EDN: " (reason e)) what
                      (str "Check that the --" (name flag) " file is complete EDN, with every bracket closed.")))))))

(defn explore!
  "Loads `path` (checkpoint or bundle) and writes the Proof Explorer to out-dir. Returns the data.
  Throws an ex-info with :error/category :view/refused when an input is wrong (see run)."
  [path out-dir {:keys [roots modules lean loop loop-report offline tree-cap]}]
  (let [loop (read-edn :loop loop)
        lean (read-edn :lean lean)
        loop-report (read-edn :loop-report loop-report)
        {:keys [env base-env source claims]} (load-source path {:modules (csv modules) :loop loop})
        roots (if roots
                (for [a (csv roots)]
                  (or (environment/resolve-id env (symbol a))
                      (refuse! (str "no declaration named " a) (str "--roots " a)
                               (str "Check the name (lein show <name> <module> prints a declaration); a declaration that "
                                    "a proof module adds needs that module in --modules."))))
                (keep #(environment/resolve-id env %) (keys claims)))
        roots (doall roots)
        data (explorer-data env {:roots roots :lean (if (map? lean) (:results lean) lean) :loop loop :loop-report loop-report
                                 :source source :base-env base-env :claims claims :tree-cap (if tree-cap (parse-long tree-cap) 600)})]
    (try (write-page! out-dir "scripts/proof-explorer.html" "data.json" data offline)
         (catch Exception e
           (refuse! (reason e) (str "-> " out-dir)
                    "Check that the output directory is writable, and run explore from the Rainbow directory (it reads scripts/proof-explorer.html).")))
    data))

(def ^:private usage
  "usage: lein explore <checkpoint.edn.gz | bundle.edn> [out-dir] [--roots a,b] [--modules ns,..] [--lean f] [--loop f] [--loop-report f] [--tree-cap n] [--offline]")

(def ^:private value-flags #{:roots :modules :lean :loop :loop-report :tree-cap})

(defn usage-problem
  "What is wrong with an explore command line, or nil: no source named, more than two positional
  arguments, an unknown option, an option without its value, or a --tree-cap that is not a positive
  whole number."
  [args]
  (let [[pos opts] (parse-args args #{"--offline"})]
    (cond (empty? pos) "name a checkpoint or proof bundle"
          (> (count pos) 2) (str "more than a source and an output directory: " (string/join " " pos))
          :else (or (some (fn [[k v]]
                            (cond (not (or (value-flags k) (= :offline k))) (str "unknown option --" (name k))
                                  (and (value-flags k) (or (not (string? v)) (string/starts-with? v "--")))
                                  (str "--" (name k) " needs a value")))
                          opts)
                    (when-let [c (:tree-cap opts)]
                      (when-not (some-> (parse-long c) pos?) (str "--tree-cap needs a positive whole number, not " c)))))))

(defn run
  "lein explore: writes the Proof Explorer; returns the exit code (0 written and every claim checked,
  1 a claim does not match its record or an input is refused, 2 a usage error). Every refusal (a
  missing or unreadable file, a file that is neither a bundle nor a checkpoint, a checkpoint that does
  not replay, an unknown root or module) prints one `FAIL explore <what> -- <why> -- <what to check>`
  line, and no page is written."
  [args]
  (let [[[path out] opts] (parse-args args #{"--offline"})]
    (if-let [problem (usage-problem args)]
      (do (when path (println (str "explore: " problem))) (println usage) 2)
      (try
        (let [out (or out "explorer") data (explore! path out opts) ex (filter :examples (:nodes data))]
          (println "wrote" (str out "/index.html") "and data.json:" (count (:nodes data)) "declarations," (count (:roots data)) "roots,"
                   (count ex) "with kernel-computed examples," (count (filter :lean (:nodes data))) "Lean badges,"
                   (count (filter :how (:nodes data))) "loop badges")
          (doseq [cl (:claims data)] (println "claim" (:alias cl) (if (:ok cl) "checked" "DOES NOT MATCH ITS RECORD")))
          (if (every? :ok (:claims data)) 0 1))
        (catch clojure.lang.ExceptionInfo e
          (let [{:explore/keys [what check] :as d} (ex-data e)]
            (if (= :view/refused (:error/category d))
              (println "FAIL explore" (or what path) "--" (.getMessage e) "--" (or check source-check))
              (println "FAIL explore" path "--" (reason e) "-- Check the source file and the options; lein verify --bundle <file> checks a bundle on its own.")))
          1)
        (catch Throwable e
          (println "FAIL explore" path "--" (reason e) "-- Check the source file and the options; lein verify --bundle <file> checks a bundle on its own.")
          1)))))

(defn -main [& args]
  (let [code (run args)]
    (shutdown-agents)
    (System/exit code)))
