(ns rainbow.proof
  "Immutable proof states and kernel-checked terminal reconstruction."
  (:require [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]))

(defn hole [id] [:hole id])
(defn hole? [value] (and (vector? value) (= :hole (first value)) (= 2 (count value))))

(defn replace-hole [partial id replacement]
  (cond
    (= partial (hole id)) replacement
    (not (vector? partial)) partial
    :else (mapv #(replace-hole % id replacement) partial)))

(defn contains-holes? [partial]
  (cond
    (hole? partial) true
    (vector? partial) (boolean (some contains-holes? partial))
    :else false))

(defn term-axioms
  "Computes the explicit transitive axiom closure of a proof term."
  [checked-environment proof-term]
  (reduce
   (fn [result id]
     (if-let [declaration (environment/declaration checked-environment id)]
       (cond-> (into result (:rainbow/axioms declaration))
         (= :axiom (:rainbow/kind declaration)) (conj id))
       result))
   #{}
   (term/constants proof-term)))

(defn close-over-context
  "Abstracts an open term over an innermost-first local context."
  [context expression constructor]
  (reduce (fn [body {:goal/keys [type mode]}]
            (constructor type body (or mode :explicit)))
          expression
          context))

;; ---- untrusted search-side conversion: fast answers the kernel would give; it rechecks every proof ----
(defn application-spine [expression]
  (loop [current expression arguments []]
    (if (= :app (first current)) (recur (second current) (into [(nth current 2)] arguments)) [current arguments])))

(def ^:private memos (atom {}))
(defn memoized
  "A pure function of (environment, key), remembered for the latest environment: 256 results per
  `kind` (65536 for ::infer), so a search pays for a normal form, type or hash once."
  [kind environment key compute]
  (let [[latest cache] (get @memos kind)]
    (if-let [hit (and (identical? latest environment) (find cache key))]
      (val hit)
      (let [value (compute)]
        (swap! memos update kind (fn [[latest cache]] (if (and (identical? latest environment) (< (count cache) (if (= kind ::infer) 65536 256)))
                                                        [latest (assoc cache key value)] [environment {key value}])))
        value))))

(defn normal [environment expression]
  (memoized ::normal environment expression #(:term (kernel/normalize environment expression))))

(def ^:private numerals #{(second @#'kernel/zero-term) (second @#'kernel/succ-term)})
(defn- head-view [environment expression]   ; the kernel's own whnf (read-only use), or nil
  (try (first (#'kernel/whnf* environment expression 100000 #{})) (catch clojure.lang.ExceptionInfo _ nil)))

(defn rigid-view
  "The whnf of `expression` when its head fixes its normal form's outer shape (Pi, sort, bound
  variable, or a non-numeral constant: whnf leaves no redex at a constant head), else nil."
  [environment expression]
  (let [view (head-view environment expression) [head arguments] (application-spine view)]
    (when (case (first head) (:pi :sort) (empty? arguments) :bound true :const (not (numerals (second head))) false)
      view)))

(defn distinct-normal-forms?
  "True only when the normal forms differ (so kernel definitional equality, which compares them up
  to levels, is false): rigid views differ in shape, head, arity or a corresponding part."
  [environment left right depth]
  (let [l (when (and (pos? depth) (not= left right)) (rigid-view environment left))
        r (when l (rigid-view environment right))
        [lh la] (application-spine l) [rh ra] (application-spine r)
        different? #(distinct-normal-forms? environment %1 %2 (dec depth))]
    (boolean
     (when r
       (cond (not= (first lh) (first rh)) true
             (= :sort (first lh)) false
             (= :pi (first lh)) (or (not= (nth lh 3) (nth rh 3)) (different? (second lh) (second rh))
                                    (different? (nth lh 2) (nth rh 2)))
             (or (not= (second lh) (second rh)) (not= (count la) (count ra))) true
             :else (some true? (map different? la ra)))))))

(defn convertible? [environment left right & _]   ; = (true? (kernel/definitionally-equal? ...))
  (and (not (distinct-normal-forms? environment left right 24))
       (true? (kernel/definitionally-equal? environment left right))))

(defn rigidly-free?
  "True only when bound `index` survives in the normal form: it occurs at a rigid head or in a part
  of a Pi or of an application with a constant or variable head."
  [environment expression index depth]
  (let [view (when (pos? depth) (head-view environment expression))
        [head arguments] (application-spine view)
        free? #(rigidly-free? environment %1 %2 (dec depth))]
    (boolean (case (first head)
               :bound (or (= index (second head)) (some #(free? % index) arguments))
               :pi (or (free? (second head) index) (free? (nth head 2) (inc index)))
               :const (some #(free? % index) arguments)
               false))))

(defn- in-context
  "The kernel's own infer* / check* run directly in a goal's context (which proof states build from
  checked types) instead of re-checking that context for each candidate."
  [operation environment context expression & expected]
  (try (clojure.core/apply operation environment (mapv :goal/type context) expression expected)
       (catch Exception exception   ; a malformed term fails here too (no assert-term! walk)
         {:status :rejected :error (ex-data exception) :message (ex-message exception)})))

(defn check-in-context
  ([environment context expression expected] (check-in-context environment context expression expected #{}))
  ([environment context expression expected _universe-parameters]
   (in-context #(do (#'kernel/check* %1 %2 %3 %4) {:status :checked :term %3 :type %4})
               environment context expression expected)))

(defn infer-in-context [environment context expression _universe-parameters]
  (memoized
   ::infer environment [(mapv :goal/type context) expression]
   ;; an application the kernel must reject (a part fails, the function's type is no Pi, or the
   ;; argument's type is certainly not its domain) is rejected without normalizing anything
   (fn [] (let [part (fn [e] (:type (infer-in-context environment context e nil)))
                [function argument] (when (= :app (first expression)) (map part (rest expression)))
                view (when function (memoized ::view environment function (fn [] (rigid-view environment function))))]
      (if (and (= :app (first expression))
               (or (nil? function) (nil? argument)
                   (and view (or (not= :pi (first view)) (distinct-normal-forms? environment (second view) argument 24)))))
        {:status :rejected :error {:error/category :proof/certain-type-mismatch}}
        (in-context #(hash-map :status :checked :type (#'kernel/infer* %1 %2 %3)) environment context expression))))))

(defn session-id [environment target context universes]
  (canonical/content-id
   {:environment (environment/environment-id environment)
    :target target
    :context (mapv :goal/type context)
    :universes (vec (sort-by str universes))}))

(defn start
  ([environment target] (start environment target {}))
  ([environment target {:keys [context names universes]
                        :or {context [] names [] universes []}}]
   (let [context (mapv (fn [index type]
                         {:goal/name (or (nth names index nil)
                                         (symbol (str "h" index)))
                          :goal/type type
                          :goal/mode :explicit})
                       (range)
                       context)
         target-check (if (empty? context)
                        (kernel/infer environment target (set universes))
                        (kernel/infer environment
                                      (close-over-context context target term/pi-term)
                                      (set universes)))
         target-kind (when (= :checked (:status target-check))
                       (:term (kernel/normalize environment (:type target-check))))]
     (if-not (and (= :checked (:status target-check))
                  (= :sort (first target-kind)))
       {:status :rejected
        :error {:error/category :proof/invalid-target
                :cause target-check}}
       (let [root-id (session-id environment target context universes)]
         {:status :ready
          :state {:rainbow/kind :proof-state
                  :proof/schema-version 1
                  :proof/session-id root-id
                  :proof/environment environment
                  :proof/root-goal target
                  :proof/root-context context
                  :proof/universes (set universes)
                  :proof/goals [{:goal/id "g-0"
                                 :goal/context context
                                 :goal/target target
                                 :goal/path []}]
                  :proof/partial-term (hole "g-0")
                  :proof/next-id 1
                  :proof/history []
                  :proof/attempted #{}
                  :proof/metrics {:kernel-checks 1 :branches 0}}})))))

(defn current-goal [state]
  (first (:proof/goals state)))

(defn fresh-goal-id [state]
  (str "g-" (:proof/next-id state)))

(defn fail-result [state tactic category detail]
  {:status :failure
   :state state
   :failure {:failure/category category
             :failure/tactic tactic
             :failure/detail detail}})

(defn progress
  "Replaces the focused goal and either returns a new state or kernel-checks a terminal term."
  [state replacement new-goals event]
  (let [focused (current-goal state)
        updated (-> state
                    (assoc :proof/partial-term
                           (replace-hole (:proof/partial-term state)
                                         (:goal/id focused)
                                         replacement))
                    (assoc :proof/goals
                           (into (vec new-goals) (rest (:proof/goals state))))
                    (update :proof/next-id + (count new-goals))
                    (update :proof/history conj event)
                    (update-in [:proof/metrics :kernel-checks] (fnil inc 0)))]
    (if (seq (:proof/goals updated))
      {:status :progress :state updated :goals (:proof/goals updated) :event event}
      (if (contains-holes? (:proof/partial-term updated))
        (fail-result state (:event/tactic event) :proof/orphan-hole
                     {:partial-term (:proof/partial-term updated)})
        (let [environment (:proof/environment state)
              proof-term (:proof/partial-term updated)
              expected (close-over-context (:proof/root-context state)
                                           (:proof/root-goal state)
                                           term/pi-term)
              closed-proof (close-over-context (:proof/root-context state)
                                               proof-term
                                               term/lambda-term)
              checked (kernel/check environment closed-proof expected
                                    (:proof/universes state))]
          (if (= :checked (:status checked))
            {:status :proved
             :proof {:rainbow/kind :checked-proof
                     :proof/term closed-proof
                     :proof/type expected
                     :proof/environment-id (environment/environment-id environment)
                     :proof/axioms (term-axioms environment closed-proof)
                     :proof/history (:proof/history updated)}
             :state updated
             :kernel checked
             :event event}
            (fail-result state (:event/tactic event) :proof/kernel-rejected-terminal
                         {:kernel checked})))))))
