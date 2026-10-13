(ns rainbow.math.tautology
  "Bounded classical propositional proof synthesis as ordinary proof data."
  (:require [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]))

(def protected-aliases
  ['proposition/truth 'proposition/falsity 'proposition/conjunction
   'proposition/equivalence 'proposition/disjunction])

(defn- application-spine [expression]
  (loop [current expression arguments []]
    (if (= :app (first current))
      (recur (second current) (into [(nth current 2)] arguments))
      [current arguments])))

(defn- apply-terms [function & arguments]
  (reduce term/application function arguments))

(defn- beta-head [expression]
  (loop [current expression]
    (case (first current)
      :let (recur (term/instantiate (nth current 3) (nth current 2)))
      :app (let [function (beta-head (second current))]
             (if (= :lam (first function))
               (recur (term/instantiate (nth function 2) (nth current 2)))
               [:app function (nth current 2)]))
      current)))

(defn- unfold-focus-head [checked-environment expression]
  (let [protected
        (into #{} (keep #(environment/resolve-id checked-environment %))
              protected-aliases)]
    (loop [current (beta-head expression) remaining 16]
      (let [[head arguments] (application-spine current)
            id (when (= :const (first head)) (second head))
            declaration (when id
                          (environment/declaration checked-environment id))]
        (if (and (pos? remaining) declaration
                 (not (contains? protected id))
                 (= :definition (:rainbow/kind declaration))
                 (:rainbow/value declaration)
                 (contains? #{:reducible :semireducible}
                            (:rainbow/transparency declaration)))
          (let [value
                (term/instantiate-universes
                 (:rainbow/value declaration)
                 (zipmap (:rainbow/universes declaration) (nth head 2)))
                unfolded (beta-head (reduce term/application value arguments))]
            (if (= current unfolded)
              current
              (recur unfolded (dec remaining))))
          current)))))

(defn- lower-body [body]
  (try (term/shift body -1)
       (catch clojure.lang.ExceptionInfo _ nil)))

(declare formula)

(defn- binary-formula [checked-environment op original arguments]
  (when (= 2 (count arguments))
    {:op op :term original
     :left (formula checked-environment (first arguments))
     :right (formula checked-environment (second arguments))}))

(defn formula [checked-environment expression]
  (let [exposed (unfold-focus-head checked-environment expression)
        [head arguments] (application-spine exposed)
        id (when (= :const (first head)) (second head))
        resolve #(environment/resolve-id checked-environment %)]
    (cond
      (= id (resolve 'proposition/truth)) {:op :truth :term expression}
      (= id (resolve 'proposition/falsity)) {:op :falsity :term expression}
      (= id (resolve 'proposition/conjunction))
      (binary-formula checked-environment :and expression arguments)
      (= id (resolve 'proposition/disjunction))
      (binary-formula checked-environment :or expression arguments)
      (= id (resolve 'proposition/equivalence))
      (binary-formula checked-environment :iff expression arguments)
      (= :pi (first exposed))
      (if-let [body (lower-body (nth exposed 2))]
        {:op :implication :term expression
         :left (formula checked-environment (second exposed))
         :right (formula checked-environment body)}
        {:op :atom :term expression})
      :else {:op :atom :term expression})))

(defn- atoms [node]
  (case (:op node)
    :atom [(:term node)]
    (:truth :falsity) []
    (:and :or :iff :implication)
    (into (atoms (:left node)) (atoms (:right node)))))

(defn- constant [checked-environment alias]
  (when-let [id (environment/resolve-id checked-environment alias)]
    (term/constant id [])))

(defn- same? [checked-environment left right]
  (true? (kernel/definitionally-equal? checked-environment left right)))

(defn- valuation-entry [checked-environment valuation atom]
  (some #(when (same? checked-environment atom (:atom %)) %) valuation))

(defn- shifted-valuation [valuation]
  (mapv (fn [entry]
          (-> entry
              (update :atom term/shift 1)
              (update :evidence term/shift 1)))
        valuation))

(declare synthesize)

(defn- synthesize-and [checked-environment constants node valuation]
  (let [left (synthesize checked-environment constants (:left node) valuation)
        right (synthesize checked-environment constants (:right node) valuation)
        left-term (get-in node [:left :term])
        right-term (get-in node [:right :term])
        formula-term (:term node)]
    (cond
      (and (:truth? left) (:truth? right))
      {:truth? true
       :evidence (apply-terms (:conjoin constants) left-term right-term
                              (:evidence left) (:evidence right))}
      (not (:truth? left))
      {:truth? false
       :evidence
       [:lam formula-term
        (apply-terms
         (term/shift (:evidence left) 1)
         (apply-terms (:left constants)
                      (term/shift left-term 1) (term/shift right-term 1)
                      (term/bound 0)))
        :explicit]}
      :else
      {:truth? false
       :evidence
       [:lam formula-term
        (apply-terms
         (term/shift (:evidence right) 1)
         (apply-terms (:right constants)
                      (term/shift left-term 1) (term/shift right-term 1)
                      (term/bound 0)))
        :explicit]})))

(defn- synthesize-or [checked-environment constants node valuation]
  (let [left (synthesize checked-environment constants (:left node) valuation)
        right (synthesize checked-environment constants (:right node) valuation)
        left-term (get-in node [:left :term])
        right-term (get-in node [:right :term])
        formula-term (:term node)]
    (cond
      (:truth? left)
      {:truth? true
       :evidence (apply-terms (:left-disjunct constants) left-term right-term
                              (:evidence left))}
      (:truth? right)
      {:truth? true
       :evidence (apply-terms (:right-disjunct constants) left-term right-term
                              (:evidence right))}
      :else
      {:truth? false
       :evidence
       [:lam formula-term
        (apply-terms (:use-disjunction constants)
                     (term/shift left-term 1) (term/shift right-term 1)
                     (:falsity constants) (term/bound 0)
                     (term/shift (:evidence left) 1)
                     (term/shift (:evidence right) 1))
        :explicit]})))

(defn- synthesize-implication
  [checked-environment constants node valuation]
  (let [left (synthesize checked-environment constants (:left node) valuation)
        right (synthesize checked-environment constants (:right node) valuation)
        left-term (get-in node [:left :term])
        right-term (get-in node [:right :term])
        formula-term (:term node)]
    (if (or (not (:truth? left)) (:truth? right))
      {:truth? true
       :evidence
       (if (:truth? right)
         [:lam left-term (term/shift (:evidence right) 1) :explicit]
         [:lam left-term
          (apply-terms (:explode constants) (term/shift right-term 1)
                       (apply-terms (term/shift (:evidence left) 1)
                                    (term/bound 0)))
          :explicit])}
      {:truth? false
       :evidence
       [:lam formula-term
        (apply-terms
         (term/shift (:evidence right) 1)
         (apply-terms (term/bound 0) (term/shift (:evidence left) 1)))
        :explicit]})))

(defn- implication-proof [constants domain codomain domain-result codomain-result]
  (if (:truth? codomain-result)
    [:lam domain (term/shift (:evidence codomain-result) 1) :explicit]
    [:lam domain
     (apply-terms (:explode constants) (term/shift codomain 1)
                  (apply-terms (term/shift (:evidence domain-result) 1)
                               (term/bound 0)))
     :explicit]))

(defn- synthesize-iff [checked-environment constants node valuation]
  (let [left (synthesize checked-environment constants (:left node) valuation)
        right (synthesize checked-environment constants (:right node) valuation)
        left-term (get-in node [:left :term])
        right-term (get-in node [:right :term])
        formula-term (:term node)]
    (if (= (:truth? left) (:truth? right))
      {:truth? true
       :evidence
       (apply-terms
        (:equivalence-intro constants) left-term right-term
        (implication-proof constants left-term right-term left right)
        (implication-proof constants right-term left-term right left))}
      {:truth? false
       :evidence
       (if (:truth? left)
         [:lam formula-term
          (apply-terms
           (term/shift (:evidence right) 1)
           (apply-terms (:equivalence-forward constants)
                        (term/shift left-term 1) (term/shift right-term 1)
                        (term/bound 0) (term/shift (:evidence left) 1)))
          :explicit]
         [:lam formula-term
          (apply-terms
           (term/shift (:evidence left) 1)
           (apply-terms (:equivalence-backward constants)
                        (term/shift left-term 1) (term/shift right-term 1)
                        (term/bound 0) (term/shift (:evidence right) 1)))
          :explicit])})))

(defn synthesize [checked-environment constants node valuation]
  (case (:op node)
    :atom (valuation-entry checked-environment valuation (:term node))
    :truth {:truth? true :evidence (:trivial constants)}
    :falsity {:truth? false
              :evidence [:lam (:term node) (term/bound 0) :explicit]}
    :and (synthesize-and checked-environment constants node valuation)
    :or (synthesize-or checked-environment constants node valuation)
    :implication
    (synthesize-implication checked-environment constants node valuation)
    :iff (synthesize-iff checked-environment constants node valuation)))

(defn prove
  "Returns a complete classical proof term for a bounded tautology, else nil."
  ([checked-environment target] (prove checked-environment target {}))
  ([checked-environment target {:keys [max-atoms] :or {max-atoms 4}}]
   (let [constants
         {:falsity (constant checked-environment 'proposition/falsity)
          :trivial (constant checked-environment 'proposition/trivial)
          :conjoin (constant checked-environment 'proposition/conjoin)
          :left (constant checked-environment 'proposition/left)
          :right (constant checked-environment 'proposition/right)
          :left-disjunct (constant checked-environment
                                   'proposition/left-disjunct)
          :right-disjunct (constant checked-environment
                                    'proposition/right-disjunct)
          :use-disjunction (constant checked-environment
                                     'proposition/use-disjunction)
          :explode (constant checked-environment 'proposition/explode)
          :equivalence-intro (constant checked-environment
                                       'proposition/equivalence-intro)
          :equivalence-forward (constant checked-environment
                                         'proposition/equivalence-forward)
          :equivalence-backward (constant checked-environment
                                          'proposition/equivalence-backward)
          :classical-cases (constant checked-environment
                                     'logic/classical-cases)}
         initial (formula checked-environment target)
         atom-terms (vec (distinct (atoms initial)))]
     (when (and (<= (count atom-terms) max-atoms)
                (every? some? (vals constants)))
       (letfn [(build [current-target remaining valuation]
                 (if-let [atom (first remaining)]
                   (let [shifted-target (term/shift current-target 1)
                         shifted-rest (mapv #(term/shift % 1) (next remaining))
                         shifted-atom (term/shift atom 1)
                         shifted (shifted-valuation valuation)
                         positive
                         (build shifted-target shifted-rest
                                (conj shifted {:atom shifted-atom
                                               :truth? true
                                               :evidence (term/bound 0)}))
                         not-atom [:pi atom (:falsity constants) :explicit]
                         negative
                         (build shifted-target shifted-rest
                                (conj shifted {:atom shifted-atom
                                               :truth? false
                                               :evidence (term/bound 0)}))]
                     (when (and positive negative)
                       (apply-terms
                        (:classical-cases constants) atom current-target
                        [:lam atom positive :explicit]
                        [:lam not-atom negative :explicit])))
                   (let [result (synthesize checked-environment constants
                                            (formula checked-environment
                                                     current-target)
                                            valuation)]
                     (when (:truth? result) (:evidence result)))))]
         (when-let [proof-term (build target atom-terms [])]
           {:proof/term proof-term
            :atoms atom-terms
            :atom-count (count atom-terms)
            :truth-table-rows (bit-shift-left 1 (count atom-terms))}))))))
