(ns rainbow.simp
  "Untrusted simp-like engine for the search. Rules are equations and implications from the reuse
  index (only entries the index's policy admits, so a hold-out applies) and from the local context;
  rule left-hand sides are indexed by head symbol and arity and matched first-order, universe
  levels included. A goal is opened through reducible definitions, then closed by assumption,
  by definitional reflexivity, by backward chaining (a rule's premises discharged recursively, to a
  depth limit), or by rewriting bottom-up to a fixpoint (step budget, visited-term memo) and closing
  what remains. Proofs are plain terms: Leibniz transports (Eq A x y := forall P, P x -> P y), so no
  equality lemma is needed. The search hands each to tactic/exact or tactic/refine; the kernel
  checks it like any other step."
  (:require [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

;; ---- budget -----------------------------------------------------------------------------------
(def ^:dynamic ^:private *fuel* nil)
(def ^:dynamic ^:private *failed* nil)   ; [ctx goal] -> the largest depth it failed at, per call
(defn- spend! []
  (when (neg? (swap! *fuel* dec)) (throw (ex-info "simp budget exhausted" {::budget true}))))

;; ---- metavariables: constants no environment holds, so the kernel never sees one -------------------
(def ^:private meta-prefix "sha256:simp-meta-")
(defn- meta-term [k] [:const (str meta-prefix k) []])
(defn- meta-index [t]
  (when (and (= :const (first t)) (.startsWith ^String (second t) meta-prefix))
    (Long/parseLong (subs (second t) (count meta-prefix)))))
(defn- metas [t] (into #{} (keep #(when (vector? %) (meta-index %))) (tree-seq vector? seq t)))
(defn- level-meta? [p] (.startsWith (name p) "simp-l"))

(defn- beta
  "Full beta (and let) normal form, no unfolding."
  [t]
  (spend!)
  (case (first t)
    :app (let [f (beta (second t)) a (beta (nth t 2))]
           (if (= :lam (first f)) (beta (term/instantiate (nth f 2) a)) [:app f a]))
    (:lam :pi) [(first t) (beta (second t)) (beta (nth t 2)) (nth t 3)]
    :let (beta (term/instantiate (nth t 3) (nth t 2)))
    t))

(defn- eq-id [env] (proof/memoized ::eq env nil #(environment/resolve-id env 'equality/Eq)))
(defn- whnf [env t] (beta (tactic/unfold-head env (beta t) #{(eq-id env)})))
(defn- eq-view [env t]
  (let [[h args] (proof/application-spine t)]
    (when (and (= :const (first h)) (= (eq-id env) (second h)) (= 3 (count args))) args)))
(defn- size [t] (if (vector? t) (reduce + 1 (map size t)) 0))

;; ---- matching -----------------------------------------------------------------------------------
(defn- lower [t d] (if (zero? d) t (try (term/shift t (- d)) (catch clojure.lang.ExceptionInfo _ nil))))

(defn- match-level [p l s]
  (when s
    (cond (and (= :param (first p)) (level-meta? (second p)))
          (if-let [v (get-in s [:levels (second p)])]
            (when (term/level-equivalent? v l) s)
            (assoc-in s [:levels (second p)] l))
          (and (= (first p) (first l)) (= (count p) (count l)) (not= :param (first p)) (not= :zero (first p)))
          (or (reduce (fn [s [a b]] (or (match-level a b s) (reduced nil))) s (map vector (rest p) (rest l)))
              (when (empty? (filter level-meta? (term/level-params p))) (when (term/level-equivalent? p l) s)))
          (empty? (filter level-meta? (term/level-params p))) (when (term/level-equivalent? p l) s))))

(defn- match
  "Extends substitution s so that pattern p (with metavariables) equals t, d binders deep."
  [p t d s]
  (when s
    (spend!)
    (if-let [k (meta-index p)]
      (if-let [v (get-in s [:terms k])]
        (when (= (term/shift v d) t) s)
        (when-let [v (lower t d)] (assoc-in s [:terms k] v)))
      (case (first p)
        :app (when (= :app (first t)) (match (nth p 2) (nth t 2) d (match (second p) (second t) d s)))
        (:lam :pi) (when (= (first p) (first t))
                     (match (nth p 2) (nth t 2) (inc d) (match (second p) (second t) d s)))
        :const (when (and (= :const (first t)) (= (second p) (second t)) (= (count (nth p 2)) (count (nth t 2))))
                 (reduce (fn [s [a b]] (or (match-level a b s) (reduced nil))) s (map vector (nth p 2) (nth t 2))))
        :sort (when (= :sort (first t)) (match-level (second p) (second t) s))
        (when (= p t) s)))))

(defn- subst
  "Replaces assigned metavariables (and level metavariables) of s in t."
  [t s]
  (let [levels (:levels s) at (fn [ls] (if (seq levels) (mapv #(term/instantiate-level % levels) ls) ls))]
    (letfn [(walk [t d]
              (case (first t)
                :const (if-let [k (meta-index t)]
                         (if-let [v (get-in s [:terms k])] (term/shift v d) t)
                         [:const (second t) (at (nth t 2))])
                :sort (if (seq levels) [:sort (term/instantiate-level (second t) levels)] t)
                :app [:app (walk (second t) d) (walk (nth t 2) d)]
                (:lam :pi) [(first t) (walk (second t) d) (walk (nth t 2) (inc d)) (nth t 3)]
                :let [:let (walk (second t) d) (walk (nth t 2) d) (walk (nth t 3) (inc d))]
                t))]
      (walk t 0))))

;; ---- rules --------------------------------------------------------------------------------------
(defn- open-rule
  "A rule from a proof head of `type`: binders become metavariables 0..n-1, opened through
  reducible definitions. :equation [A l r] when the stated conclusion is an Eq."
  [env type head]
  (loop [t (beta type) k 0 binders []]
    (let [u (if (= :pi (first t)) t (whnf env t))]
      (if (and (= :pi (first u)) (< k 16))
        (recur (beta (term/instantiate (nth u 2) (meta-term k))) (inc k) (conj binders (second u)))
        (let [concl u
              dependent (into #{} (mapcat metas) (conj binders concl))]
          {:head head :binders binders :concl concl :dependent dependent
           :equation (eq-view env t)})))))

(defn- key-of [t]
  (let [[h args] (proof/application-spine t)]
    (case (first h) :const (when-not (meta-index h) [(second h) (count args)]) :bound [h (count args)] nil)))

(defn- orient
  "Rewrite directions for an equation rule: l -> r when r's metavariables are l's and l is no bare
  metavariable; the smaller side is preferred as the result, ties keep the stated direction."
  [{[_ l r] :equation :as rule}]
  (let [ok? (fn [from to] (and (key-of from) (every? (metas from) (metas to))))
        forward (when (ok? l r) (assoc rule :lhs l :rhs r :direction :forward))
        backward (when (ok? r l) (assoc rule :lhs r :rhs l :direction :backward))]
    (cond (and forward backward) [(if (< (size l) (size r)) backward forward)]
          :else (keep identity [forward backward]))))

(defn- rule-index [rules k] (group-by #(or (k %) :any) rules))

(defn- declaration-rule
  "A theorem's rule, its universe parameters renamed to level metavariables."
  [env id]
  (let [d (environment/declaration env id) us (:rainbow/universes d)
        renamed (zipmap us (map (fn [i] [:param (symbol (str "simp-l" i))]) (range)))]
    (binding [*fuel* (atom 1000000)]
      (try (assoc (open-rule env (term/instantiate-universes (:rainbow/type d) renamed) [:const id (mapv renamed us)]) :id id)
           (catch Exception _ nil)))))

(def ^:private env-cache (atom nil))
(defn- environment-rules
  "Every theorem's rules, indexed, built once per environment; which of them a search may use is
  decided per lookup (see `admitted`)."
  [env]
  (let [[e rules] @env-cache]
    (if (identical? e env)
      rules
      (let [opened (into [] (keep #(when (= :theorem (:rainbow/kind (environment/declaration env %)))
                                     (declaration-rule env %)))
                         (:rainbow.environment/order env))
            rules {:close (rule-index opened (comp key-of :concl))
                   :rewrite (rule-index (mapcat orient (filter :equation opened)) (comp key-of :lhs))}]
        (reset! env-cache [env rules])
        rules))))

(defn- admitted
  "The index rules of `kind` at key k that the search may use: entries the index's policy admits
  (reuse/admits), so a hold-out applies."
  [cfg kind k]
  (when-let [admit (:admit cfg)] (filter (comp admit :id) (get-in cfg [:rules kind k]))))

(defn- local-type [ctx i] (term/shift (nth ctx i) (inc i)))

(defn- local-rules
  "Rules from the context: each local, and the two halves of a local conjunction."
  [env ctx]
  (let [conj-id (environment/resolve-id env 'proposition/conjunction)
        facts (for [i (range (count ctx))
                    :let [t (beta (tactic/unfold-head env (local-type ctx i) #{(eq-id env) conj-id}))
                          [h [a b]] (proof/application-spine t)]
                    fact (if (and conj-id (= [:const conj-id []] h) b)
                           ;; h : A /\ B is forall D, (A -> B -> D) -> D: h A (fn a b => a) proves A
                           (let [half (fn [x pick] [x [:app [:app [:bound i] x]
                                                       [:lam a [:lam (term/shift b 1) [:bound pick] :explicit] :explicit]]])]
                             [[t [:bound i]] (half a 1) (half b 0)])
                           [[t [:bound i]]])]
                fact)
        opened (keep (fn [[t h]] (try (open-rule env t h) (catch clojure.lang.ExceptionInfo _ nil))) facts)]
    {:close (rule-index opened (comp key-of :concl))
     :rewrite (rule-index (mapcat orient (filter :equation opened)) (comp key-of :lhs))
     :facts (mapv (fn [[t h]] [t h]) facts)}))

;; ---- proof construction --------------------------------------------------------------------------
(def ^:private prop [:sort [:zero]])
(defn- refl [A l] [:lam [:pi A prop :explicit] [:lam [:app [:bound 0] (term/shift l 1)] [:bound 0] :explicit] :explicit])
(defn- apply-terms [f args] (reduce term/application f args))

(defn- abstract
  "t with every free occurrence of u (closed in t's context) replaced by bound 0 of a new binder."
  [t u]
  (letfn [(walk [node d]
            (cond (= node (term/shift u d)) [:bound d]
                  :else (case (first node)
                          :bound (if (>= (second node) d) [:bound (inc (second node))] node)
                          :app [:app (walk (second node) d) (walk (nth node 2) d)]
                          (:lam :pi) [(first node) (walk (second node) d) (walk (nth node 2) (inc d)) (nth node 3)]
                          :let [:let (walk (second node) d) (walk (nth node 2) d) (walk (nth node 3) (inc d))]
                          node)))]
    (walk t 0)))

(defn- transport
  "A proof of t from a proof of t', where t' is t with u rewritten by h : Eq A l r (u = l when
  :forward, u = r when :backward)."
  [t u A h direction]
  (let [body (abstract t u)]
    (if (= :backward direction)
      (fn [p] (apply-terms h [[:lam A body :explicit] p]))                  ; h M : M l -> M r
      (fn [p] (apply-terms h [[:lam A [:pi body (term/shift t 2) :explicit] :explicit]   ; (M z -> t)
                              [:lam t [:bound 0] :explicit] p])))))

;; ---- closing ------------------------------------------------------------------------------------
(declare close normalize)

(defn- intros [env ctx t]
  (loop [ctx ctx t t binders []]
    (let [u (whnf env t)]
      (if (and (= :pi (first u)) (< (count binders) 24))
        (recur (into [(second u)] ctx) (nth u 2) (conj binders u))
        [ctx u binders]))))

(defn- wrap [binders p] (reduce (fn [b [_ domain _ mode]] [:lam domain b mode]) p (rseq binders)))

(defn- convertible? [env l r]
  (or (= l r) (binding [kernel/*reduction-budget* 200000] (proof/convertible? env l r))))

(defn- solve
  "Completes s over rule binders k.. in order: assigned by matching, a premise closed recursively, or
  a dependent binder tried with each local of its type. Returns the full substitution or nil."
  [env cfg ctx locals rule s k depth]
  (if (= k (count (:binders rule)))
    s
    (let [next #(solve env cfg ctx locals rule (assoc-in s [:terms k] %) (inc k) depth)]
      (if (get-in s [:terms k])
        (solve env cfg ctx locals rule s (inc k) depth)
        (let [goal (beta (subst (nth (:binders rule) k) s))]
          (when (empty? (metas goal))
            (if (contains? (:dependent rule) k)
              ;; a local of the binder's type, or the value a later premise gets by matching a local
              (some next (take 8 (distinct
                                  (concat (keep (fn [[t h]] (when (= goal t) h)) (:facts locals))
                                          (for [premise (subvec (:binders rule) (inc k)) [t _] (:facts locals)
                                                :let [v (get-in (match (subst premise s) t 0 s) [:terms k])] :when v]
                                            v)))))
              (some-> (close env cfg ctx goal (dec depth)) next))))))))

(defn- instance [rule s] (apply-terms (subst (:head rule) s) (map #(get-in s [:terms %]) (range (count (:binders rule))))))

(defn- chain [env cfg ctx locals t depth]
  (let [k (key-of t)]
    (some (fn [rule] (some->> (match (:concl rule) t 0 {}) (#(solve env cfg ctx locals rule % 0 depth)) (instance rule)))
          (concat (get-in locals [:close k]) (take 32 (admitted cfg :close k)) (get-in locals [:close :any])))))

(defn- close
  "A proof of t in ctx, or nil: intros through reducible definitions, then assumption, definitional
  reflexivity, backward chaining, or rewriting followed by closing."
  [env cfg ctx t depth]
  (spend!)
  (when-not (some-> (get @*failed* [ctx t]) (>= depth))
    (let [[ctx0 t0] [ctx t]
          [ctx t binders] (intros env ctx (beta t))
          locals (local-rules env ctx)
          [A l r] (eq-view env t)
          p (or (some (fn [[u h]] (when (= u t) h)) (:facts locals))
                (when (and A (convertible? env l r)) (refl A l))
                (when (pos? depth) (chain env cfg ctx locals t depth))
                (when (pos? depth)
                  (let [[t' back] (normalize env cfg ctx locals t (dec depth))]
                    (when (not= t' t)
                      (some-> (close env cfg ctx t' (dec depth)) back)))))]
      (if p (wrap binders p) (do (swap! *failed* assoc [ctx0 t0] depth) nil)))))

;; ---- rewriting ----------------------------------------------------------------------------------
(defn- subterms
  "Rewritable subterms of t, innermost first: those free only in t's context, lowered to it."
  [t]
  (letfn [(walk [node d]
            (concat (case (first node)
                      :app (concat (walk (second node) d) (walk (nth node 2) d))
                      (:lam :pi) (concat (walk (second node) d) (walk (nth node 2) (inc d)))
                      nil)
                    (when (#{:app :const :bound} (first node)) (some-> (lower node d) vector))))]
    (distinct (walk t 0))))

(defn- rewrites
  "Each one-step rewrite of t: [t' proof-of-t-from-proof-of-t']."
  [env cfg ctx locals t depth]
  (for [u (subterms t)
        :let [k (key-of u)]
        :when k
        rule (concat (get-in locals [:rewrite k]) (admitted cfg :rewrite k))
        :let [s (some->> (match (:lhs rule) u 0 {}) (#(solve env cfg ctx locals rule % 0 depth)))]
        :when s
        :let [v (beta (subst (:rhs rule) s))]
        :when (not= u v)]
    [(beta (term/instantiate (abstract t u) v))
     (transport t u (beta (subst (first (:equation rule)) s)) (instance rule s) (:direction rule))]))

(defn- normalize
  "Rewrites t to a fixpoint within the budget (at most 64 steps), never revisiting a term."
  [env cfg ctx locals t depth]
  (loop [t t back identity seen #{t} steps 0]
    (if-let [[t' step] (when (< steps 64) (first (remove #(seen (first %)) (rewrites env cfg ctx locals t depth))))]
      (recur t' (comp back step) (conj seen t') (inc steps))
      [t back])))

;; ---- search entry point -------------------------------------------------------------------------
(defn steps
  "Search steps for the focused goal of `state`: a closing :exact, else a :refine to the rewritten
  goal. Untrusted; tactic/exact and the terminal kernel check decide."
  [state {:keys [reuse-index reuse-policy simp-fuel simp-depth]}]
  (let [root? (empty? (:proof/history state))   ; the root gets a large budget, later states a small one
        simp-fuel (or simp-fuel (if root? 100000 5000))
        simp-depth (or simp-depth 6)
        env (:proof/environment state)
        goal (proof/current-goal state)
        ctx (mapv :goal/type (:goal/context goal))
        target (:goal/target goal)]
    (when (eq-id env)
      (binding [*fuel* (atom simp-fuel) *failed* (atom {})]
        (try
          (let [cfg (when reuse-index
                      (let [admit (reuse/admits reuse-index env (merge reuse/default-policy reuse-policy) nil)]
                        {:rules (environment-rules env) :admit (memoize #(admit [:const % []]))}))]
            ;; iterative deepening: shallow proofs first, failures remembered per depth
            (if-let [p (some #(close env cfg ctx target %) (range (inc simp-depth)))]
              [{:tactic :exact :term p :source :native-simp :focus/phase :invertible}]
              (let [locals (local-rules env ctx)
                    t (beta target)
                    [t' back] (normalize env cfg ctx locals t (dec simp-depth))]
                (when (not= t' t)
                  [{:tactic :refine :template (back [:hole 0]) :targets [t'] :source :native-simp
                    :focus/phase :equality}]))))
          (catch clojure.lang.ExceptionInfo e
            (when-not (::budget (ex-data e)) (throw e))
            nil))))))
