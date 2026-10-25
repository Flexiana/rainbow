(ns rainbow.search
  "Deterministic bounded baseline search over observable proof states."
  (:require [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.tautology :as tautology]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term])
  (:import (java.lang.management ManagementFactory)))

(def default-budget
  {:states 1000
   :depth 32
   :wall-ms 10000
   ;; Dependent prefix synthesis is selected per problem after dogfooding; it
   ;; is intentionally off for workloads whose stroke budget did not price it.
   :local-application-depth 0
   :local-application-terms 0
   :local-application-compositional? false
   :global-application-terms []
   :native-logic-focus? false
   :native-logic-prune? false
   :native-reducible-focus? false
   :native-classical-cases? false
   :native-classical-tautology? false
   :native-equality-rewrite? false
   :native-proposition-extensionality? false
   :native-function-extensionality? false
   :native-structural-theorem-reuse? false
   :native-bool-cases? false
   :native-inductive-cases? false
   :native-focused-intro? false
   :native-finite-witnesses? false
   :native-list-cover-witnesses? false
   :native-finite-cover-reuse? false
   :native-premise-theorem-reuse? false
   :native-dependent-theorem-specialization? false
   :related-reuse-limit 8})

(defn- current-thread-cpu-ms []
  (let [bean (ManagementFactory/getThreadMXBean)]
    (if (.isCurrentThreadCpuTimeSupported bean)
      (max 0 (long (/ (.getCurrentThreadCpuTime bean) 1000000)))
      0)))

(defn- used-memory-mb []
  (let [runtime (Runtime/getRuntime)]
    (max 0 (long (/ (- (.totalMemory runtime) (.freeMemory runtime)) 1048576)))))

(defn goal-hash [environment goal]
  (canonical/content-id
   {:environment (environment/environment-id environment)
    :context (mapv (fn [local]
                     (:term (kernel/normalize environment (:goal/type local))))
                   (:goal/context goal))
    :target (:term (kernel/normalize environment (:goal/target goal)))}))

(defn state-hash [state]
  (canonical/content-id
   {:environment (environment/environment-id (:proof/environment state))
    :universes (vec (sort-by str (:proof/universes state)))
    :goals (mapv (fn [goal]
                   {:context (mapv :goal/type (:goal/context goal))
                    :target (:goal/target goal)})
                 (:proof/goals state))}))

(defn attempt-key [goal-hash step]
  (canonical/content-id {:goal/hash goal-hash :strategy step}))

(defn failure-keys [attempts]
  (into #{}
        (keep (fn [attempt]
                (when (= :failure (:result attempt))
                  (attempt-key (:goal/hash attempt) (:strategy attempt)))))
        attempts))

(defn- step-key [environment goal step]
  (attempt-key (goal-hash environment goal) step))

(defn- local-application-terms
  "Enumerates well-typed applications of local functions to local evidence.

  This is deliberately an untrusted, bounded search aid. Each prefix is kept
  only when kernel inference succeeds in the current context, and any terminal
  proof still goes through the ordinary tactic and kernel reconstruction path."
  [state max-depth max-terms extra-seeds compositional?]
  (let [goal (proof/current-goal state)
        context (:goal/context goal)
        checked-environment (:proof/environment state)
        universes (:proof/universes state)
        seeds (vec (distinct
                    (concat (map (comp term/bound int)
                                 (range (count context)))
                            extra-seeds)))]
    (loop [frontier seeds
           depth 0
           seen (set seeds)
           applications []]
      (if (or (>= depth max-depth)
              (empty? frontier)
              (>= (count applications) max-terms))
        applications
        (let [arguments (if compositional?
                          (vec (concat seeds applications))
                          seeds)
              {:keys [next seen applications]}
              (reduce
               (fn [{:keys [next seen applications] :as result} function]
                 (if (>= (count applications) max-terms)
                   (reduced result)
                   (reduce
                    (fn [{:keys [next seen applications] :as inner} argument]
                      (if (>= (count applications) max-terms)
                        (reduced inner)
                        (let [candidate (term/application function argument)]
                          (if (contains? seen candidate)
                            inner
                            (let [inferred
                                  (proof/infer-in-context
                                   checked-environment context candidate universes)]
                              (if (= :checked (:status inferred))
                                {:next (conj next candidate)
                                 :seen (conj seen candidate)
                                 :applications (conj applications candidate)}
                                inner))))))
                    result arguments)))
               {:next [] :seen seen :applications applications}
               frontier)]
          (recur (if compositional?
                   (vec (concat seeds applications))
                   next)
                 (inc depth) seen applications))))))

(defn- dependent-reuse-specializations
  "Kernel-infers bounded applications of retrieved dependent theorems to
  locals in the current context.

  `tactic/apply` intentionally rejects an unspecialized dependent Pi because
  it cannot create sound independent subgoals for later binders.  This helper
  instead supplies already-existing local terms one binder at a time, retaining
  only prefixes whose types the kernel can infer.  Returned terms remain
  untrusted tactic candidates."
  [state candidates max-depth max-terms]
  (let [goal (proof/current-goal state)
        checked-environment (:proof/environment state)
        context (:goal/context goal)
        universes (:proof/universes state)
        arguments (mapv (comp term/bound int) (range (count context)))
        specialize-one
        (fn [candidate]
          (loop [frontier [(:reuse/term candidate)]
                 depth 0
                 seen #{(:reuse/term candidate)}
                 result []]
            (if (or (>= depth max-depth)
                    (empty? frontier)
                    (>= (count result) max-terms))
              result
              (let [next
                    (->> (for [function frontier argument arguments]
                           (term/application function argument))
                         (remove seen)
                         distinct
                         (filter
                          (fn [expression]
                            (= :checked
                               (:status
                                (proof/infer-in-context
                                 checked-environment context expression
                                 universes)))))
                         (take (- max-terms (count result)))
                         vec)]
                (recur next (inc depth) (into seen next)
                       (into result
                             (map #(assoc candidate :reuse/term %) next)))))))]
    (->> candidates
         (mapcat specialize-one)
         (take max-terms)
         vec)))

(defn- application-spine [expression]
  (loop [current expression
         arguments []]
    (if (= :app (first current))
      (recur (second current) (into [(nth current 2)] arguments))
      [current arguments])))

(defn- beta-head [expression]
  (loop [current expression]
    (case (first current)
      :let (recur (term/instantiate (nth current 3) (nth current 2)))
      :app (let [function (beta-head (second current))]
             (if (= :lam (first function))
               (recur (term/instantiate (nth function 2) (nth current 2)))
               [:app function (nth current 2)]))
      current)))

(defn- pi-conclusion-head
  "Returns the syntactic application head after a theorem's Pi prefix.

  Bound occurrences in the conclusion are intentionally left open: routing
  needs only the stable head constructor, while the kernel validates every
  later specialization."
  [expression]
  (loop [current (beta-head expression)]
    (if (= :pi (first current))
      (recur (beta-head (nth current 2)))
      (first (application-spine current)))))

(defn- matching-conclusion-head?
  [checked-environment target candidate]
  (let [declaration
        (environment/declaration checked-environment
                                 (:reuse/declaration-id candidate))
        target-head (first (application-spine (beta-head target)))
        candidate-head (when declaration
                         (pi-conclusion-head (:rainbow/type declaration)))
        target-id (when (= :const (first target-head))
                    (second target-head))
        candidate-id (when (= :const (first candidate-head))
                       (second candidate-head))
        equivalence-heads
        (into #{} (keep #(environment/resolve-id checked-environment %))
              ['proposition/equivalence 'proposition/conjunction])]
    (and target-id candidate-id
         (or (= target-id candidate-id)
             ;; Native surface helpers encode Iff directly as its constructive
             ;; conjunction, while imported targets retain the reducible Iff
             ;; alias. Treat those two heads as one routing family; the kernel
             ;; still checks the fully specialized term definitionally.
             (and (contains? equivalence-heads target-id)
                  (contains? equivalence-heads candidate-id))))))

(def focus-protected-aliases
  "Native connective heads retained as proof-search vocabulary rather than
  unfolded into their lower-level encodings."
  ['proposition/truth 'proposition/falsity 'proposition/conjunction
   'proposition/equivalence 'proposition/disjunction 'proposition/existence
   'proposition/unique-existence 'equality/Eq])

(defn- unfold-reducible-focus-head
  "Exposes reducible proposition combinators while preserving connective heads.

  This is an untrusted focusing aid. The kernel still checks every tactic term,
  and bounded unfolding cannot change which terms are accepted."
  [checked-environment expression]
  (let [protected-ids
        (into #{} (keep #(environment/resolve-id checked-environment %))
              focus-protected-aliases)]
    (loop [current (beta-head expression) remaining 16]
      (let [[head arguments] (application-spine current)
            id (when (= :const (first head)) (second head))
            declaration (when id
                          (environment/declaration checked-environment id))]
        (if (and (pos? remaining)
                 declaration
                 (not (contains? protected-ids id))
                 (= :definition (:rainbow/kind declaration))
                 (:rainbow/value declaration)
                 (contains? #{:reducible :semireducible}
                            (:rainbow/transparency declaration)))
          (let [parameters (:rainbow/universes declaration)
                levels (nth head 2)
                value (term/instantiate-universes
                       (:rainbow/value declaration)
                       (zipmap parameters levels))
                unfolded (beta-head (reduce term/application value arguments))]
            (if (= current unfolded)
              current
              (recur unfolded (dec remaining))))
          current)))))

(defn- apply-terms [function & arguments]
  (reduce term/application function arguments))

(defn- conjunction-components [checked-environment expression]
  (let [[head arguments] (application-spine expression)]
    (when (and (= :const (first head))
               (= (environment/resolve-id checked-environment
                                           'proposition/conjunction)
                  (second head))
               (= 2 (count arguments)))
      arguments)))

(declare native-constant)

(defn- disjunction-refinement-step
  "Builds a direct plan from `(A ∧ P) ∨ (Q ∧ B)` to `A ∨ B`.

  Either conjunct may supply its branch result. This captures the reusable
  refinement-forgetting pattern behind Xor elimination without naming Xor or
  trusting a new kernel rule."
  [checked-environment goal universes target-arguments]
  (let [[target-left target-right] target-arguments
        constant #(native-constant checked-environment % [])
        use-disjunction (constant 'proposition/use-disjunction)
        left-disjunct (constant 'proposition/left-disjunct)
        right-disjunct (constant 'proposition/right-disjunct)
        project-left (constant 'proposition/left)
        project-right (constant 'proposition/right)]
    (when (every? some? [use-disjunction left-disjunct right-disjunct
                         project-left project-right])
      (some
       (fn [[index _local]]
         (let [evidence (term/bound index)
               inferred (proof/infer-in-context
                         checked-environment (:goal/context goal) evidence
                         universes)
               current-type (when (= :checked (:status inferred))
                              (unfold-reducible-focus-head
                               checked-environment (:type inferred)))
               [head branches] (if current-type
                                 (application-spine current-type) [nil []])]
           (when (and (= :const (first head))
                      (= (environment/resolve-id checked-environment
                                                  'proposition/disjunction)
                         (second head))
                      (= 2 (count branches)))
             (let [[left-branch right-branch] branches
                   left-components (conjunction-components
                                    checked-environment left-branch)
                   right-components (conjunction-components
                                     checked-environment right-branch)
                   projection
                   (fn [components wanted]
                     (cond
                       (= wanted (first components)) project-left
                       (= wanted (second components)) project-right
                       :else nil))
                   left-project (and left-components
                                     (projection left-components target-left))
                   right-project (and right-components
                                      (projection right-components target-right))]
               (when (and left-project right-project)
                 (let [branch-proof
                       (fn [branch components project constructor]
                         (let [[first-component second-component] components]
                           [:lam branch
                            (apply-terms
                             constructor
                             (term/shift target-left 1)
                             (term/shift target-right 1)
                             (apply-terms
                              project
                              (term/shift first-component 1)
                              (term/shift second-component 1)
                              (term/bound 0)))
                            :explicit]))]
                   {:tactic :exact
                    :term
                    (apply-terms
                     use-disjunction left-branch right-branch
                     (:goal/target goal) evidence
                     (branch-proof left-branch left-components left-project
                                   left-disjunct)
                     (branch-proof right-branch right-components right-project
                                   right-disjunct))
                    :source :structural-proof-plan
                    :focus/phase :invertible}))))))
       (map-indexed vector (:goal/context goal))))))

(defn- contains-subterm?
  "True when needle occurs structurally in an open core term.

  Equality endpoints inferred from a local and the current goal live in the
  same de Bruijn context, so structural occurrence is the precise cheap gate
  needed before proposing an untrusted rewrite branch."
  [expression needle]
  (or (= expression needle)
      (and (vector? expression)
           (boolean (some #(contains-subterm? % needle) expression)))))

(defn- contains-free-bound?
  "Tests whether a local de Bruijn index occurs free, respecting binders."
  ([expression index] (contains-free-bound? expression index 0))
  ([expression index depth]
   (case (first expression)
     :bound (= (second expression) (+ index depth))
     (:sort :const) false
     :app (or (contains-free-bound? (second expression) index depth)
              (contains-free-bound? (nth expression 2) index depth))
     (:lam :pi)
     (or (contains-free-bound? (second expression) index depth)
         (contains-free-bound? (nth expression 2) index (inc depth)))
     :let
     (or (contains-free-bound? (second expression) index depth)
         (contains-free-bound? (nth expression 2) index depth)
         (contains-free-bound? (nth expression 3) index (inc depth)))
     false)))

(defn- native-constant [checked-environment alias levels]
  (when-let [id (environment/resolve-id checked-environment alias)]
    [:const id (vec levels)]))

(def ^:private native-witness-candidate-limit
  "Caps constructor synthesis before it competes for the global state budget."
  16)

(defn- checked-term-of-type?
  [checked-environment context universes expected candidate]
  (when candidate
    (let [inferred (proof/infer-in-context checked-environment context
                                           candidate universes)]
      (and (= :checked (:status inferred))
           (true? (kernel/definitionally-equal?
                   checked-environment (:type inferred) expected))))))

(defn- local-terms-of-type
  [checked-environment context universes expected]
  (keep (fn [index]
          (let [candidate (term/bound index)]
            (when (checked-term-of-type? checked-environment context universes
                                         expected candidate)
              candidate)))
        (range (count context))))

(defn- native-list-witness-candidates
  "Synthesizes a small typed portfolio when an existential ranges over List.

  Empty, singleton, prefixed, and appended enumerations cover the common
  constructive shapes behind finite empty/singleton/insert/union proofs. This
  is only an untrusted proposal generator: every candidate is inferred in the
  current dependent context and every completed proof is still kernel checked."
  [state carrier normalized-carrier]
  (let [checked-environment (:proof/environment state)
        goal (proof/current-goal state)
        context (:goal/context goal)
        universes (:proof/universes state)
        [carrier-head carrier-arguments] (application-spine normalized-carrier)
        list-id (environment/resolve-id checked-environment 'data/List)]
    (when (and (= :const (first carrier-head))
               (= list-id (second carrier-head))
               (= 1 (count carrier-arguments)))
      (let [levels (nth carrier-head 2)
            element (first carrier-arguments)
            nil-constructor (native-constant checked-environment 'data/nil
                                             levels)
            cons-constructor (native-constant checked-environment 'data/cons
                                              levels)
            append (native-constant checked-environment 'list/append levels)
            empty (when nil-constructor
                    (apply-terms nil-constructor element))
            elements (vec (take 4 (local-terms-of-type checked-environment
                                                       context universes
                                                       element)))
            enumerations
            (vec (take 4 (local-terms-of-type checked-environment context
                                             universes carrier)))
            singletons (when (and cons-constructor empty)
                         (map #(apply-terms cons-constructor element % empty)
                              elements))
            prefixed (when cons-constructor
                       (for [value elements enumeration enumerations]
                         (apply-terms cons-constructor element value
                                      enumeration)))
            appended (when append
                       (for [left enumerations right enumerations]
                         (apply-terms append element left right)))]
        (->> (concat [empty] enumerations singletons prefixed appended)
             distinct
             (filter #(checked-term-of-type? checked-environment context
                                             universes carrier %))
             (take native-witness-candidate-limit))))))

(defn- native-finite-subset-reuse-steps
  "Specializes the generalized finite-subset theorem from local proof data.

  The result proposition fixes the element type and smaller set; a local
  finiteness hypothesis supplies the larger set. Applying the resulting
  partial term leaves only subset evidence and the already-local finiteness
  premise. This is an untrusted proof-plan proposal and cannot bypass tactic
  reconstruction or the kernel."
  [state]
  (let [checked-environment (:proof/environment state)
        goal (proof/current-goal state)
        target (:goal/target goal)
        [target-head target-arguments] (application-spine target)
        finite-id (environment/resolve-id checked-environment 'set/finite)
        theorem (when (and (= :const (first target-head))
                           (= finite-id (second target-head))
                           (= 2 (count target-arguments)))
                  (native-constant checked-environment
                                   'set/finite-subset-preserved
                                   (nth target-head 2)))]
    (if-not theorem
      []
      (let [[element small] target-arguments]
        (->> (:goal/context goal)
             (map-indexed vector)
             (keep
              (fn [[index local]]
                (let [inferred
                      (proof/infer-in-context
                       checked-environment (:goal/context goal)
                       (term/bound index) (:proof/universes state))
                      [local-head local-arguments]
                      (when (= :checked (:status inferred))
                        (application-spine (:type inferred)))]
                  (when (and local-head (= :const (first local-head))
                             (= finite-id (second local-head))
                             (= 2 (count local-arguments))
                             (true? (kernel/definitionally-equal?
                                     checked-environment element
                                     (first local-arguments))))
                    {:tactic :apply
                     :term (apply-terms theorem element small
                                        (second local-arguments))
                     :source :structural-theorem-reuse
                     :reuse/kind :finite-subset-preservation
                     :reuse/local-index index
                     :focus/phase :invertible}))))
             vec)))))

(defn- bool-constructor-conflict-step
  "Eliminates an equality between Bool's distinct nullary constructors.

  The term is a derived Leibniz-equality discriminator: transport `True`
  through the equality using a Bool-recursive predicate whose opposite branch
  is the current goal. It is an ordinary proof term, not a kernel rule."
  [checked-environment target evidence carrier left right]
  (let [normalize #(:term (kernel/normalize checked-environment %))
        bool (native-constant checked-environment 'data/Bool [])
        false-term (native-constant checked-environment 'data/false [])
        true-term (native-constant checked-environment 'data/true [])
        bool-rec (native-constant checked-environment 'data/Bool.rec
                                  [[:succ term/zero-level]])
        truth (native-constant checked-environment 'proposition/truth [])
        trivial (native-constant checked-environment 'proposition/trivial [])
        normalized-carrier (normalize carrier)
        normalized-left (normalize left)
        normalized-right (normalize right)
        orientation
        (cond
          (and (= normalized-left false-term)
               (= normalized-right true-term)) :false-to-true
          (and (= normalized-left true-term)
               (= normalized-right false-term)) :true-to-false
          :else nil)]
    (when (and orientation (= normalized-carrier bool)
               bool-rec truth trivial)
      (let [proposition-sort (term/sort-term term/zero-level)
            motive (term/lambda-term bool proposition-sort)
            shifted-target (term/shift target 1)
            [false-branch true-branch]
            (if (= :false-to-true orientation)
              [truth shifted-target]
              [shifted-target truth])
            predicate
            (term/lambda-term
             bool
             (apply-terms bool-rec motive false-branch true-branch
                          (term/bound 0)))]
        {:tactic :exact
         :term (apply-terms evidence predicate trivial)
         :source :native-constructor-discrimination
         :focus/phase :invertible}))))

(defn- leibniz-bool-conflict-arguments
  "Recovers Bool constructor endpoints from the normalized Leibniz encoding
  `forall P : Bool -> Prop, P left -> P right`."
  [checked-environment expression]
  (let [bool (native-constant checked-environment 'data/Bool [])]
    (when (and (= :pi (first expression))
               (= :pi (first (second expression)))
               (= bool (second (second expression)))
               (= (term/sort-term term/zero-level)
                  (nth (second expression) 2))
               (= :pi (first (nth expression 2))))
      (let [premise (second (nth expression 2))
            conclusion (nth (nth expression 2) 2)]
        (when (and (= :app (first premise))
                   (= (term/bound 0) (second premise))
                   (= :app (first conclusion))
                   (= (term/bound 1) (second conclusion)))
          [bool (nth premise 2) (nth conclusion 2)])))))

(defn- classical-case-step
  "Selects one occurring, undecided local proposition for excluded-middle
  case analysis. The split theorem and every resulting branch remain ordinary
  proof terms checked by the kernel."
  [state target]
  (let [goal (proof/current-goal state)
        checked-environment (:proof/environment state)
        context (:goal/context goal)
        universes (:proof/universes state)
        proposition-sort (term/sort-term term/zero-level)
        falsity (native-constant checked-environment 'proposition/falsity [])
        cases (native-constant checked-environment 'logic/classical-cases [])
        inferred-type
        (fn [index]
          (let [inferred (proof/infer-in-context
                          checked-environment context (term/bound index)
                          universes)]
            (when (= :checked (:status inferred)) (:type inferred))))
        context-types (mapv inferred-type (range (count context)))
        decided?
        (fn [atom]
          (let [not-atom (when falsity [:pi atom falsity :explicit])]
            (boolean
             (some
              (fn [local-type]
                (and local-type
                     (or (true? (kernel/definitionally-equal?
                                 checked-environment local-type atom))
                         (and not-atom
                              (true? (kernel/definitionally-equal?
                                      checked-environment local-type
                                      not-atom))))))
              context-types))))
        atom
        (when (and cases falsity)
          (some
           (fn [index]
             (let [candidate (term/bound index)
                   candidate-type (nth context-types index)]
               (when (and candidate-type
                          (true? (kernel/definitionally-equal?
                                  checked-environment candidate-type
                                  proposition-sort))
                          (contains-subterm? target candidate)
                          (not (decided? candidate)))
                 candidate)))
           (range (count context))))]
    (when atom
      {:tactic :apply
       :term (apply-terms cases atom target)
       :source :classical-proof-plan
       :focus/phase :choice
       :case/atom atom})))

(defn- lower-binder-term [expression]
  (try
    (term/shift expression -1)
    (catch clojure.lang.ExceptionInfo _ nil)))

(defn- unique-equality-step
  "Recognizes singleton equality predicates under unique existence and
  instantiates the corresponding checked, universe-polymorphic theorem.

  This is deliberately a narrow typed matcher: the emitted term is still sent
  through `exact` and the ordinary kernel boundary."
  [checked-environment target]
  (let [[head arguments] (application-spine target)
        unique-id (environment/resolve-id checked-environment
                                          'proposition/unique-existence)
        equality-id (environment/resolve-id checked-environment 'equality/Eq)]
    (when (and (= :const (first head)) (= unique-id (second head))
               (= 2 (count arguments)))
      (let [[carrier predicate] arguments]
        (when (= :lam (first predicate))
          (let [domain (second predicate)
                body (nth predicate 2)
                [eq-head eq-arguments] (application-spine body)]
            (when (and (= :const (first eq-head))
                       (= equality-id (second eq-head))
                       (= 3 (count eq-arguments))
                       (= (term/shift carrier 1) (first eq-arguments))
                       (= carrier domain))
              (let [[_ left right] eq-arguments
                    [alias value]
                    (cond
                      (= right (term/bound 0))
                      ['proposition/unique-equality-left
                       (lower-binder-term left)]

                      (= left (term/bound 0))
                      ['proposition/unique-equality-right
                       (lower-binder-term right)]

                      :else [nil nil])
                    theorem (when alias
                              (native-constant checked-environment alias
                                               (nth head 2)))]
                (when (and theorem value)
                  {:tactic :exact
                   :term (apply-terms theorem carrier value)
                   :source :structural-theorem-reuse
                   :focus/phase :invertible})))))))))

(defn- structural-symmetry-equivalence-step
  "Builds direct proof-plan fragments for symmetry relations that recur as
  equivalence subgoals. All open terms are shifted under generated lambdas and
  the final candidate is still checked by `exact`."
  [checked-environment left right]
  (let [id #(environment/resolve-id checked-environment %)
        constant #(native-constant checked-environment %1 (or %2 []))
        [left-head left-arguments] (application-spine left)
        [right-head right-arguments] (application-spine right)
        left-id (when (= :const (first left-head)) (second left-head))
        right-id (when (= :const (first right-head)) (second right-head))
        intro (constant 'proposition/equivalence-intro [])]
    (when intro
      (cond
        (and (= left-id (id 'equality/Eq)) (= right-id left-id)
             (= 3 (count left-arguments)) (= 3 (count right-arguments))
             (= (first left-arguments) (first right-arguments))
             (= (second left-arguments) (nth right-arguments 2))
             (= (nth left-arguments 2) (second right-arguments)))
        (let [[carrier from to] left-arguments
              levels (nth left-head 2)
              symmetric (constant 'equality/symmetric levels)
              forward
              [:lam left
               (apply-terms symmetric
                            (term/shift carrier 1)
                            (term/shift from 1) (term/shift to 1)
                            (term/bound 0))
               :explicit]
              backward
              [:lam right
               (apply-terms symmetric
                            (term/shift carrier 1)
                            (term/shift to 1) (term/shift from 1)
                            (term/bound 0))
               :explicit]]
          {:tactic :exact
           :term (apply-terms intro left right forward backward)
           :source :structural-proof-plan
           :focus/phase :invertible})

        (and (= left-id (id 'proposition/equivalence))
             (= right-id left-id)
             (= 2 (count left-arguments)) (= 2 (count right-arguments))
             (= (first left-arguments) (second right-arguments))
             (= (second left-arguments) (first right-arguments)))
        (let [[from to] left-arguments
              equivalence-intro intro
              forward-elim (constant 'proposition/equivalence-forward [])
              backward-elim (constant 'proposition/equivalence-backward [])
              swapped
              (fn [domain from to]
                (let [shifted-from (term/shift from 1)
                      shifted-to (term/shift to 1)
                      evidence (term/bound 0)]
                  [:lam domain
                   (apply-terms
                    equivalence-intro shifted-to shifted-from
                    (apply-terms backward-elim shifted-from shifted-to evidence)
                    (apply-terms forward-elim shifted-from shifted-to evidence))
                   :explicit]))]
          (when (and forward-elim backward-elim)
            {:tactic :exact
             :term (apply-terms intro left right
                                (swapped left from to)
                                (swapped right to from))
             :source :structural-proof-plan
             :focus/phase :invertible}))

        :else nil))))

(defn- definitional-equivalence-step
  "Closes equivalent reducible propositions with explicit identity functions."
  [checked-environment left right]
  (when (true? (kernel/definitionally-equal? checked-environment left right))
    (when-let [intro (native-constant checked-environment
                                      'proposition/equivalence-intro [])]
      {:tactic :exact
       :term (apply-terms intro left right
                          [:lam left (term/bound 0) :explicit]
                          [:lam right (term/bound 0) :explicit])
       :source :structural-proof-plan
       :focus/phase :invertible})))

(defn- disjunction-map-term
  "Constructs a map between disjunctions whose conjunction branches differ
  only by forgotten refinements, conjunct order, or branch order."
  [checked-environment source-original target-original]
  (let [source (unfold-reducible-focus-head checked-environment source-original)
        target (unfold-reducible-focus-head checked-environment target-original)
        [source-head source-branches] (application-spine source)
        [target-head target-branches] (application-spine target)
        disjunction-id (environment/resolve-id checked-environment
                                               'proposition/disjunction)
        constant #(native-constant checked-environment % [])
        use-disjunction (constant 'proposition/use-disjunction)
        left-disjunct (constant 'proposition/left-disjunct)
        right-disjunct (constant 'proposition/right-disjunct)
        conjoin (constant 'proposition/conjoin)
        project-left (constant 'proposition/left)
        project-right (constant 'proposition/right)
        same? #(true? (kernel/definitionally-equal?
                       checked-environment %1 %2))]
    (when (and (= :const (first source-head))
               (= disjunction-id (second source-head))
               (= :const (first target-head))
               (= disjunction-id (second target-head))
               (= 2 (count source-branches))
               (= 2 (count target-branches))
               (every? some? [use-disjunction left-disjunct right-disjunct
                              conjoin project-left project-right]))
      (let [[source-left source-right] source-branches
            [target-left target-right] target-branches
            branch-proof
            (fn [source-branch target-branch constructor]
              (let [source-components
                    (conjunction-components checked-environment source-branch)
                    target-components
                    (conjunction-components checked-environment target-branch)
                    project
                    (fn [wanted]
                      (cond
                        (same? wanted (first source-components)) project-left
                        (same? wanted (second source-components)) project-right
                        :else nil))
                    first-project (and source-components target-components
                                       (project (first target-components)))
                    second-project (and source-components target-components
                                        (project (second target-components)))
                    transformed
                    (cond
                      (same? source-branch target-branch) (term/bound 0)
                      (and first-project second-project)
                      (apply-terms
                       conjoin
                       (term/shift (first target-components) 2)
                       (term/shift (second target-components) 2)
                       (apply-terms
                        first-project
                        (term/shift (first source-components) 2)
                        (term/shift (second source-components) 2)
                        (term/bound 0))
                       (apply-terms
                        second-project
                        (term/shift (first source-components) 2)
                        (term/shift (second source-components) 2)
                        (term/bound 0)))
                      :else nil)]
                (when transformed
                  [:lam (term/shift source-branch 1)
                   (apply-terms constructor
                                (term/shift target-left 2)
                                (term/shift target-right 2)
                                transformed)
                   :explicit])))
            mapping
            (fn [left-target left-constructor right-target right-constructor]
              (let [on-left (branch-proof source-left left-target
                                          left-constructor)
                    on-right (branch-proof source-right right-target
                                           right-constructor)]
                (when (and on-left on-right)
                  [:lam source-original
                   (apply-terms use-disjunction
                                (term/shift source-left 1)
                                (term/shift source-right 1)
                                (term/shift target-original 1)
                                (term/bound 0) on-left on-right)
                   :explicit])))]
        (or (mapping target-left left-disjunct
                     target-right right-disjunct)
            (mapping target-right right-disjunct
                     target-left left-disjunct))))))

(defn- disjunction-equivalence-step
  [checked-environment left right]
  (when-let [forward (disjunction-map-term checked-environment left right)]
    (when-let [backward (disjunction-map-term checked-environment right left)]
      (when-let [intro (native-constant checked-environment
                                        'proposition/equivalence-intro [])]
        {:tactic :exact
         :term (apply-terms intro left right forward backward)
         :source :structural-proof-plan
         :focus/phase :invertible}))))

(defn- native-logic-steps
  "Builds focused steps from native connective goals and local proof data.

  These are ordinary untrusted tactic proposals. Native theorem constants are
  fully instantiated with the connective operands found in the goal/context;
  tactic application and terminal kernel checking remain authoritative."
  [state native-reducible-focus? native-classical-cases?
   native-equality-rewrite?
   native-proposition-extensionality?
   native-function-extensionality?
   native-structural-theorem-reuse?
   native-finite-witnesses? native-list-cover-witnesses?
   native-finite-cover-reuse?]
  (let [goal (proof/current-goal state)
        checked-environment (:proof/environment state)
        finite-subset-steps
        (when native-finite-cover-reuse?
          (native-finite-subset-reuse-steps state))
        target (if native-reducible-focus?
                 (unfold-reducible-focus-head checked-environment
                                              (:goal/target goal))
                 (:goal/target goal))
        [target-head target-arguments] (application-spine target)
        target-id (when (= :const (first target-head)) (second target-head))
        id #(environment/resolve-id checked-environment %)
        constant #(native-constant checked-environment %1 (or %2 []))
        goal-steps
        (cond
          (and (= target-id (id 'proposition/equivalence))
               (= 2 (count target-arguments)))
          (let [symmetry
                (when native-structural-theorem-reuse?
                  (apply structural-symmetry-equivalence-step
                         checked-environment target-arguments))
                definitional
                (when native-reducible-focus?
                  (apply definitional-equivalence-step
                         checked-environment target-arguments))
                disjunction
                (when native-reducible-focus?
                  (apply disjunction-equivalence-step
                         checked-environment target-arguments))]
            (cond-> []
              disjunction (conj disjunction)
              definitional (conj definitional)
              symmetry (conj symmetry)
              true
              (into
               (when-let [intro (constant 'proposition/equivalence-intro [])]
                 [{:tactic :apply
                   :term (apply apply-terms intro target-arguments)
                   :source :native-logic-goal :focus/phase :invertible}]))))

          (and (= target-id (id 'proposition/conjunction))
               (= 2 (count target-arguments)))
          (when-let [intro (constant 'proposition/conjoin [])]
            [{:tactic :apply
              :term (apply apply-terms intro target-arguments)
              :source :native-logic-goal :focus/phase :invertible}])

          (= target-id (id 'proposition/truth))
          (when-let [trivial (constant 'proposition/trivial [])]
            [{:tactic :exact :term trivial :source :native-logic-goal
              :focus/phase :invertible}])

          (and (= target-id (id 'proposition/disjunction))
               (= 2 (count target-arguments)))
          (let [structural
                (when native-reducible-focus?
                  (disjunction-refinement-step checked-environment goal
                                               (:proof/universes state)
                                               target-arguments))]
            (cond->
             (vec
              (keep (fn [alias]
                      (when-let [intro (constant alias [])]
                        {:tactic :apply
                         :term (apply apply-terms intro target-arguments)
                         :source :native-logic-goal :focus/phase :choice}))
                    ['proposition/left-disjunct
                     'proposition/right-disjunct]))
              structural (into [structural])))

          (and (or native-finite-witnesses? native-list-cover-witnesses?)
               (= target-id (id 'proposition/existence))
               (= 2 (count target-arguments)))
          (let [[carrier predicate] target-arguments
                witness (constant 'proposition/witness (nth target-head 2))
                normalized-carrier
                (:term (kernel/normalize checked-environment carrier))
                bool (constant 'data/Bool [])
                finite-candidates
                (when (and native-finite-witnesses?
                           (= normalized-carrier bool))
                  [(constant 'data/false []) (constant 'data/true [])])
                local-candidates
                (when native-finite-witnesses?
                  (local-terms-of-type
                   checked-environment (:goal/context goal)
                   (:proof/universes state) carrier))
                list-candidates
                (when native-list-cover-witnesses?
                  (native-list-witness-candidates state carrier
                                                  normalized-carrier))]
            (when witness
              (mapv
               (fn [candidate]
                 {:tactic :apply
                  :term (apply-terms witness carrier predicate candidate)
                  :source :native-finite-witness
                  :focus/phase :choice})
               (->> (concat finite-candidates local-candidates list-candidates)
                    distinct
                    (filter #(checked-term-of-type?
                              checked-environment (:goal/context goal)
                              (:proof/universes state) carrier %))))))

          (= target-id (id 'equality/Eq))
          (let [[carrier left right] target-arguments
                proposition-sort (term/sort-term term/zero-level)
                extensionality (constant 'logic/proposition-extensionality [])
                normalized-carrier
                (:term (kernel/normalize checked-environment carrier))
                carrier-pi (when (= :pi (first normalized-carrier))
                             normalized-carrier)
                domain (when carrier-pi (second carrier-pi))
                codomain (when carrier-pi (nth carrier-pi 2))
                codomain-outer (when codomain (lower-binder-term codomain))
                binder-mode (when carrier-pi (nth carrier-pi 3))
                domain-kind
                (when domain
                  (proof/infer-in-context checked-environment
                                          (:goal/context goal) domain
                                          (:proof/universes state)))
                codomain-kind
                (when codomain-outer
                  (proof/infer-in-context checked-environment
                                          (:goal/context goal) codomain-outer
                                          (:proof/universes state)))
                normalized-domain-kind
                (when (= :checked (:status domain-kind))
                  (:term (kernel/normalize checked-environment
                                           (:type domain-kind))))
                normalized-codomain-kind
                (when (= :checked (:status codomain-kind))
                  (:term (kernel/normalize checked-environment
                                           (:type codomain-kind))))
                domain-level (when (= :sort (first normalized-domain-kind))
                               (second normalized-domain-kind))
                codomain-level
                (when (= :sort (first normalized-codomain-kind))
                  (second normalized-codomain-kind))
                function-extensionality
                (when (and domain-level codomain-level)
                  (constant 'logic/function-extensionality
                            [domain-level codomain-level]))
                function-structural
                (when (and native-function-extensionality?
                           (= 3 (count target-arguments))
                           (= :explicit binder-mode)
                           codomain-outer
                           function-extensionality)
                  (let [value (term/bound 0)
                        point-equality
                        (apply-terms
                         (constant 'equality/Eq [codomain-level])
                         (term/shift codomain-outer 1)
                         (apply-terms (term/shift left 1) value)
                         (apply-terms (term/shift right 1) value))]
                    {:tactic :refine
                     :template
                     (apply-terms function-extensionality domain codomain-outer
                                  left right [:hole 0])
                     :targets [(term/pi-term domain point-equality :explicit)]
                     :source :structural-theorem-reuse
                     :focus/phase :equality}))
                equivalence (constant 'proposition/equivalence [])
                truth (constant 'proposition/truth [])
                equal-truth
                (or (constant 'proposition/generalized-evidence-equals-truth [])
                    (constant 'proposition/equal-truth-from-evidence []))
                symmetric (constant 'equality/symmetric (nth target-head 2))
                structural
                (when (and native-proposition-extensionality?
                           (= 3 (count target-arguments))
                           extensionality equivalence
                           (true? (kernel/definitionally-equal?
                                   checked-environment carrier proposition-sort)))
                  {:tactic :refine
                   :template (apply-terms extensionality left right [:hole 0])
                   :targets [(apply-terms equivalence left right)]
                   :source :structural-theorem-reuse
                   :focus/phase :equality})
                generalized
                (when (and native-structural-theorem-reuse?
                           (= 3 (count target-arguments))
                           equal-truth truth
                           (true? (kernel/definitionally-equal?
                                   checked-environment carrier proposition-sort)))
                  (cond
                    (= right truth)
                    {:tactic :refine
                     :template (apply-terms equal-truth left [:hole 0])
                     :targets [left]
                     :source :structural-theorem-reuse
                     :focus/phase :equality}

                    (and (= left truth) symmetric)
                    (let [forward (apply-terms equal-truth right [:hole 0])]
                      {:tactic :refine
                       :template (apply-terms symmetric carrier right truth forward)
                       :targets [right]
                       :source :structural-theorem-reuse
                       :focus/phase :equality})

                    :else nil))]
            (cond-> []
              generalized (conj generalized)
              structural (conj structural)
              function-structural (conj function-structural)
              true (conj {:tactic :reflexivity :source :native-logic-goal
                          :focus/phase :heuristic})))

          :else
          (cond-> []
            native-structural-theorem-reuse?
            (into (keep identity [(unique-equality-step checked-environment
                                                        target)]))))
        context-steps
        (mapcat
         (fn [index _local]
           (let [evidence (term/bound index)
                 inferred (proof/infer-in-context
                           checked-environment (:goal/context goal) evidence
                           (:proof/universes state))
                 current-type
                 (when (= :checked (:status inferred))
                   (if native-reducible-focus?
                     (unfold-reducible-focus-head checked-environment
                                                  (:type inferred))
                     (:type inferred)))
                 declared-type
                 (when-let [value (:goal/type _local)]
                   (if native-reducible-focus?
                     (unfold-reducible-focus-head checked-environment value)
                     value))
                 [head arguments]
                 (if current-type
                   (application-spine current-type)
                   [nil []])
                 local-id (when (= :const (first head)) (second head))
                 local-levels (when (= :const (first head)) (nth head 2))
                 leibniz-conflict
                 (when-let [[carrier left right]
                            (leibniz-bool-conflict-arguments
                             checked-environment declared-type)]
                   (bool-constructor-conflict-step
                    checked-environment target evidence carrier left right))]
             (cond
               leibniz-conflict [leibniz-conflict]

               (and (= local-id (id 'proposition/equivalence))
                    (= 2 (count arguments)))
               (keep (fn [alias]
                       (when-let [eliminate (constant alias [])]
                         {:tactic :apply
                          :term (apply apply-terms eliminate
                                       (concat arguments [evidence]))
                          :source :native-logic-context
                          :focus/phase :left}))
                     ['proposition/equivalence-forward
                      'proposition/equivalence-backward])

               (and (= local-id (id 'equality/Eq))
                    (= 3 (count arguments)))
               (let [[carrier left right] arguments
                     conflict (bool-constructor-conflict-step
                               checked-environment target evidence
                               carrier left right)]
                 (cond-> []
                   conflict (conj conflict)

                   (and native-equality-rewrite?
                        (not= left right) (contains-subterm? target left))
                   (conj {:tactic :rewrite :term evidence
                          :direction :backward
                          :source :native-logic-goal
                          :focus/phase :equality})

                   (and native-equality-rewrite?
                        (not= left right) (contains-subterm? target right))
                   (conj {:tactic :rewrite :term evidence
                          :direction :forward
                          :source :native-logic-goal
                          :focus/phase :equality})))

               (and (= local-id (id 'proposition/conjunction))
                    (= 2 (count arguments)))
               (keep (fn [alias]
                       (when-let [project (constant alias [])]
                         {:tactic :apply
                          :term (apply apply-terms project
                                       (concat arguments [evidence]))
                          :source :native-logic-context
                          :focus/phase :left}))
                     ['proposition/left 'proposition/right])

               (and (= local-id (id 'proposition/disjunction))
                    (= 2 (count arguments)))
               (when-let [eliminate (constant 'proposition/use-disjunction [])]
                 [{:tactic :apply
                   :term (apply apply-terms eliminate
                                (concat arguments [target evidence]))
                   :source :native-logic-context :focus/phase :left}])

               (and (= local-id (id 'proposition/existence))
                    (= 2 (count arguments)))
               (when-let [eliminate
                          (constant 'proposition/use-witness local-levels)]
                 [{:tactic :apply
                   :term (apply apply-terms eliminate
                                (concat arguments [target evidence]))
                   :source :native-logic-context :focus/phase :left}])

               (= local-id (id 'proposition/falsity))
               (when-let [eliminate (constant 'proposition/explode [])]
                 [{:tactic :exact
                   :term (apply-terms eliminate target evidence)
                   :source :native-logic-context :focus/phase :left}])

               :else [])))
         (range) (:goal/context goal))
        classical-step
        (when native-classical-cases?
          (classical-case-step state target))]
    (vec (distinct (concat (when classical-step [classical-step])
                           finite-subset-steps
                           goal-steps context-steps)))))

(defn- available-steps
  [state reuse-options local-application-depth
   local-application-terms-limit local-application-compositional?
   global-application-terms
   native-logic-focus? native-logic-prune? native-reducible-focus?
   native-classical-cases? native-classical-tautology?
   native-equality-rewrite?
   native-proposition-extensionality? native-function-extensionality?
   native-structural-theorem-reuse? native-bool-cases?
   native-inductive-cases? native-focused-intro? witness-options]
  (let [{:keys [reuse-index reuse-policy native-premise-theorem-reuse?
                native-dependent-theorem-specialization?
                related-reuse-limit]} reuse-options
        [native-finite-witnesses? native-list-cover-witnesses?
         native-finite-cover-reuse?]
        witness-options
        goal (proof/current-goal state)
        context (:goal/context goal)
        target
        (if native-reducible-focus?
          (unfold-reducible-focus-head (:proof/environment state)
                                       (:goal/target goal))
          (:term (kernel/normalize (:proof/environment state)
                                   (:goal/target goal))))
        lookup (when reuse-index
                 (reuse/query reuse-index (:proof/environment state)
                              (:goal/target goal) reuse-policy))
        reuse-steps (mapv (fn [candidate]
                            {:tactic :reuse
                             :term (:reuse/term candidate)
                             :declaration/id (:reuse/declaration-id candidate)
                             :score (:reuse/score candidate)})
                          (:candidates lookup))
        related-lookup
        (when (and reuse-index native-premise-theorem-reuse?)
          (reuse/query-related
           reuse-index (:proof/environment state) (:goal/target goal)
           (assoc (or reuse-policy {}) :limit (or related-reuse-limit 8))))
        exact-reuse-ids (set (map :reuse/declaration-id
                                  (:candidates lookup)))
        related-reuse-candidates
        (->> (:candidates related-lookup)
             (remove #(contains? exact-reuse-ids
                                 (:reuse/declaration-id %)))
             vec)
        specialization-candidates
        (filterv #(matching-conclusion-head?
                   (:proof/environment state) (:goal/target goal) %)
                 related-reuse-candidates)
        related-reuse-steps
        (->> related-reuse-candidates
             (keep
              (fn [candidate]
                (let [step
                      {:tactic :apply
                       :term (:reuse/term candidate)
                       :declaration/id (:reuse/declaration-id candidate)
                       :score (:reuse/score candidate)
                       :source :premise-theorem-reuse}
                      probe (tactic/run state (tactic/apply (:term step)))]
                  (when-not (contains? #{:failure :no-progress}
                                       (:status probe))
                    step))))
             vec)
        related-specialization-steps
        (when native-dependent-theorem-specialization?
          (->> (dependent-reuse-specializations
                state specialization-candidates
                local-application-depth local-application-terms-limit)
               (keep
                (fn [candidate]
                  (let [step
                        {:tactic :apply
                         :term (:reuse/term candidate)
                         :declaration/id (:reuse/declaration-id candidate)
                         :score (:reuse/score candidate)
                         :source :premise-theorem-reuse
                         :reuse/kind :dependent-prefix-specialization}
                        probe (tactic/run state (tactic/apply (:term step)))]
                    (when-not (contains? #{:failure :no-progress}
                                         (:status probe))
                      step))))
               vec))
        tautology-plan
        (when (and native-classical-tautology?
                   (not= :pi (first (:goal/target goal))))
          (tautology/prove (:proof/environment state) (:goal/target goal)
                           {:max-atoms 4}))
        tautology-step
        (when tautology-plan
          {:tactic :exact
           :term (:proof/term tautology-plan)
           :source :classical-proof-plan
           :focus/phase :invertible
           :tautology/atom-count (:atom-count tautology-plan)
           :tautology/truth-table-rows (:truth-table-rows tautology-plan)})
        bool-id (when native-bool-cases?
                  (environment/resolve-id (:proof/environment state)
                                          'data/Bool))
        bool-case-steps
        (when bool-id
          (->> context
               (map-indexed vector)
               (keep (fn [[index local]]
                       (let [[head _] (application-spine
                                      (:goal/type local))]
                         (when (and (= :const (first head))
                                    (= bool-id (second head))
                                    (contains-free-bound? (:goal/target goal)
                                                          index))
                           {:tactic :induction
                            :term [:bound index]
                            :source :native-bool-cases
                            :focus/phase :invertible}))))
               vec))
        inductive-ids
        (when native-inductive-cases?
          (into #{}
                (keep #(environment/resolve-id (:proof/environment state) %))
                ['data/Option 'data/Product 'data/Sum 'data/Subtype
                 'data/Sigma 'data/PSigma]))
        inductive-case-steps
        (when (seq inductive-ids)
          (->> context
               (map-indexed vector)
               (keep (fn [[index local]]
                       (let [[head _] (application-spine
                                      (:goal/type local))]
                         (when (and (= :const (first head))
                                    (contains? inductive-ids (second head))
                                    (contains-free-bound? (:goal/target goal)
                                                          index))
                           {:tactic :induction
                            :term [:bound index]
                            :source :native-inductive-cases
                            :focus/phase :invertible}))))
               vec))
        focused-steps
        (vec
         (concat
          (if native-logic-focus?
            (cond->
             (native-logic-steps state native-reducible-focus?
                                 native-classical-cases?
                                 native-equality-rewrite?
                                 native-proposition-extensionality?
                                 native-function-extensionality?
                                 native-structural-theorem-reuse?
                                 native-finite-witnesses?
                                 native-list-cover-witnesses?
                                 native-finite-cover-reuse?)
              tautology-step (into [tautology-step]))
            [])
          bool-case-steps
          inductive-case-steps))
        focused-goal
        (filter #(contains? #{:native-logic-goal :native-bool-cases
                              :native-inductive-cases
                              :native-constructor-discrimination
                              :native-finite-witness
                              :structural-theorem-reuse
                              :structural-proof-plan :classical-proof-plan}
                            (:source %))
                focused-steps)
        focused-context (filter #(= :native-logic-context (:source %)) focused-steps)
        invertible-goal (filter #(= :invertible (:focus/phase %)) focused-goal)
        equality-goal (filter #(= :equality (:focus/phase %)) focused-goal)
        choice-goal (filter #(= :choice (:focus/phase %)) focused-goal)
        heuristic-goal (filter #(= :heuristic (:focus/phase %)) focused-goal)
        focused-seeds (concat (keep :term focused-context)
                              global-application-terms)
        local-applications
        (local-application-terms state local-application-depth
                                 local-application-terms-limit focused-seeds
                                 local-application-compositional?)
        intro-step
        (when (= :pi (first target))
          [{:tactic :intro
            :focused-target
            (when (and native-focused-intro?
                       (not= target (:goal/target goal)))
              target)}])
        generic-steps
        (concat
         (map-indexed (fn [index _] {:tactic :apply :term [:bound index]}) context)
         (map (fn [expression]
                {:tactic :apply :term expression :source :local-application})
              local-applications))
        strategy-steps
        (if native-logic-prune?
          (cond
            (seq invertible-goal) invertible-goal
            ;; A rewrite beneath a pending Pi can expose an assumption, while
            ;; introducing that Pi may still be the productive sibling branch.
            ;; Keep both; visited-state hashing bounds rewrite oscillation.
            (seq equality-goal) (concat equality-goal intro-step)
            (seq intro-step) intro-step
            ;; Definition-aware hypotheses often expose invertible left rules
            ;; (notably Xor -> Or). Consume those before committing to a
            ;; non-invertible right-disjunction branch.
            (and native-reducible-focus? (seq focused-context))
            (concat focused-context generic-steps)
            (seq choice-goal) choice-goal
            (seq focused-context) (concat focused-context generic-steps)
            :else (concat heuristic-goal generic-steps))
          (concat focused-steps intro-step generic-steps))]
    {:lookup lookup
     :related-lookup related-lookup
     :local-application-count (count local-applications)
     :native-logic-count (count focused-steps)
     :steps
     (vec
      (concat
       reuse-steps
       related-reuse-steps
       related-specialization-steps
       [{:tactic :assumption}]
       (if (or (seq related-reuse-steps)
               (seq related-specialization-steps))
         [] strategy-steps)))}))

(defn- compile-step [step]
  (case (:tactic step)
    :intro (if-let [target (:focused-target step)]
             (tactic/intro-from target)
             (tactic/intro))
    :assumption (tactic/assumption)
    :exact (tactic/exact (:term step))
    :apply (tactic/apply (:term step))
    :refine (tactic/refine (:template step) (:targets step))
    :rewrite (tactic/rewrite (:term step) {:direction (:direction step)})
    :induction (tactic/induction (:term step))
    :reflexivity (tactic/reflexivity)
    :reuse (tactic/exact (:term step))))

(defn- attempt-record [state step result elapsed-ms]
  (let [goal (proof/current-goal state)
        base {:rainbow/kind :proof-attempt
              :attempt/schema-version 1
              :goal/hash (goal-hash (:proof/environment state) goal)
              :strategy step
              :result (case (:status result)
                        :proved :success
                        :progress :progress
                        :failure :failure
                        :no-progress :no-progress
                        (:status result))
              :failure/category (get-in result [:failure :failure/category])
              :cost {:elapsed-ms elapsed-ms}}]
    (assoc base :attempt/id
           (canonical/content-id (dissoc base :cost)))))

(defn- blocked-result [frontier dead-ends attempts metrics reason]
  (let [states (vec (concat (map first frontier) dead-ends))
        remaining (mapv (fn [state]
                          (let [goal (proof/current-goal state)]
                            {:goal-hash (goal-hash (:proof/environment state) goal)
                             :target (:goal/target goal)
                             :context (mapv :goal/type (:goal/context goal))}))
                        (take 10 states))
        failures (frequencies (keep :failure/category attempts))]
    {:status :blocked
     :reason reason
     :remaining remaining
     :dominant-failures (mapv (fn [[category count]]
                                {:class category :count count})
                              (sort-by (comp - val) failures))
     :attempts attempts
     :telemetry metrics}))

(defn prove
  "Breadth-first proof search. Its only success path is tactic reconstruction plus kernel checking."
  ([state] (prove state default-budget))
  ([state budget]
   (let [{:keys [states depth wall-ms cpu-ms memory-mb cancelled?
                 known-failures reuse-index reuse-policy]
          :as options} (merge default-budget budget)
         started (System/nanoTime)
         cpu-started (current-thread-cpu-ms)
         memory-started (used-memory-mb)
         elapsed #(long (/ (- (System/nanoTime) started) 1000000))
         cpu-elapsed #(- (current-thread-cpu-ms) cpu-started)
         memory-delta #(max 0 (- (used-memory-mb) memory-started))]
     (loop [frontier (conj clojure.lang.PersistentQueue/EMPTY [state 0])
            visited #{(state-hash state)}
            attempted (set known-failures)
            attempts []
            dead-ends []
            metrics {:states-created 1
                     :states-deduplicated 0
                     :branches-pruned 0
                     :failure-cache-hits 0
                     :max-depth 0
                     :kernel-checks 0
                     :reuse-lookups 0
                     :reuse-candidates 0
                     :reuse-attempts 0
                     :reuse-successes 0
                     :local-application-candidates 0
                     :native-logic-candidates 0}]
       ;; Publish only completed expansion counters and the current immutable
       ;; frontier. A stroke can retain this lower bound when cancelling a
       ;; worker inside a costly candidate/kernel operation. No result here is
       ;; a proof verdict, and the observer cannot bypass reconstruction.
       (when-let [publish (:progress! options)]
         (publish {:state (or (ffirst frontier) (first dead-ends))
                   :attempts attempts :telemetry (assoc metrics :wall-ms (elapsed))}))
       (cond
         (or (.isInterrupted (Thread/currentThread))
             (and (ifn? cancelled?) (cancelled?)))
         (blocked-result frontier dead-ends attempts
                         (assoc metrics :wall-ms (elapsed)) :cancelled)

         (and cpu-ms (>= (cpu-elapsed) cpu-ms))
         (blocked-result frontier dead-ends attempts
                         (assoc metrics :wall-ms (elapsed)) :cpu-budget)

         (and memory-mb (>= (memory-delta) memory-mb))
         (blocked-result frontier dead-ends attempts
                         (assoc metrics :wall-ms (elapsed)) :memory-budget)

         (empty? frontier)
         (blocked-result frontier dead-ends attempts
                         (assoc metrics :wall-ms (elapsed)) :frontier-exhausted)

         (>= (:states-created metrics) states)
         (blocked-result frontier dead-ends attempts
                         (assoc metrics :wall-ms (elapsed)) :state-budget)

         (>= (elapsed) wall-ms)
         (blocked-result frontier dead-ends attempts
                         (assoc metrics :wall-ms (elapsed)) :wall-budget)

         :else
         (let [[current current-depth] (peek frontier)
               frontier (pop frontier)]
           (if (>= current-depth depth)
             (recur frontier visited attempted attempts (conj dead-ends current)
                    (-> metrics
                        (update :branches-pruned inc)
                        (update :max-depth max current-depth)))
               (let [{:keys [steps lookup related-lookup local-application-count
                           native-logic-count]}
                   (available-steps current
                                    {:reuse-index reuse-index
                                     :reuse-policy reuse-policy
                                    :native-premise-theorem-reuse?
                                    (:native-premise-theorem-reuse? options)
                                    :native-dependent-theorem-specialization?
                                    (:native-dependent-theorem-specialization?
                                     options)
                                    :related-reuse-limit
                                     (:related-reuse-limit options)}
                                    (:local-application-depth options)
                                    (:local-application-terms options)
                                    (:local-application-compositional? options)
                                    (:global-application-terms options)
                                    (:native-logic-focus? options)
                                    (:native-logic-prune? options)
                                    (:native-reducible-focus? options)
                                    (:native-classical-cases? options)
                                    (:native-classical-tautology? options)
                                    (:native-equality-rewrite? options)
                                    (:native-proposition-extensionality? options)
                                    (:native-function-extensionality? options)
                                    (:native-structural-theorem-reuse? options)
                                    (:native-bool-cases? options)
                                    (:native-inductive-cases? options)
                                    (:native-focused-intro? options)
                                    [(:native-finite-witnesses? options)
                                     (:native-list-cover-witnesses? options)
                                     (:native-finite-cover-reuse? options)])
                   lookup? (some? lookup)
                   related-lookup? (some? related-lookup)
                   candidate-count (+ (count (:candidates lookup))
                                      (count (:candidates related-lookup)))
                   metrics (cond-> metrics
                             (pos? local-application-count)
                             (update :local-application-candidates
                                     + local-application-count)
                             (pos? native-logic-count)
                             (update :native-logic-candidates
                                     + native-logic-count)
                             (or lookup? related-lookup?)
                             (update :reuse-lookups inc)
                             (or lookup? related-lookup?)
                             (update :reuse-candidates + candidate-count))
                   outcomes
                   (reduce
                    (fn [acc step]
                      (let [key (step-key (:proof/environment current)
                                          (proof/current-goal current) step)]
                        (if (contains? attempted key)
                          (update acc :skipped inc)
                          (let [before (System/nanoTime)
                                result (tactic/run current (compile-step step))
                                cost (long (/ (- (System/nanoTime) before) 1000000))
                                record (attempt-record current step result cost)
                                failed? (contains? #{:failure :no-progress} (:status result))]
                            (-> acc
                                (cond-> failed? (update :attempted conj key))
                                (update :attempts conj record)
                                (update :results conj [result record]))))))
                    {:attempted attempted :attempts attempts :results [] :skipped 0}
                    steps)
                   proved (some (fn [[result record]]
                                  (when (= :proved (:status result)) [result record]))
                                (:results outcomes))]
               (if proved
                 (let [[proved-result proved-record] proved
                       reused? (= :reuse (get-in proved-record [:strategy :tactic]))]
                   (assoc proved-result
                        :attempts (:attempts outcomes)
                        :telemetry (-> metrics
                                       (assoc :states-created (inc (:states-created metrics))
                                              :max-depth (max (:max-depth metrics)
                                                              (inc current-depth))
                                              :wall-ms (elapsed)
                                              :attempts (count (:attempts outcomes)))
                                       (update :reuse-attempts +
                                               (count (filter #(= :reuse
                                                                  (get-in % [:strategy :tactic]))
                                                              (map second (:results outcomes)))))
                                       (update :reuse-successes + (if reused? 1 0)))))
                 (let [progressed (keep (fn [[result record]]
                                          (when (= :progress (:status result))
                                            [(update (:state result) :proof/attempted conj (:attempt/id record))
                                             (inc current-depth)]))
                                        (:results outcomes))
                       [frontier visited deduplicated created]
                       (reduce (fn [[queue seen duplicates count-created] [next-state next-depth]]
                                 (let [hash (state-hash next-state)]
                                   (if (contains? seen hash)
                                     [queue seen (inc duplicates) count-created]
                                     [(conj queue [next-state next-depth])
                                      (conj seen hash)
                                      duplicates
                                      (inc count-created)])))
                               [frontier visited 0 0]
                               progressed)]
                   (recur frontier
                          visited
                          (:attempted outcomes)
                          (:attempts outcomes)
                          (if (seq progressed)
                            dead-ends
                            (vec (take-last 10 (conj dead-ends current))))
                          (-> metrics
                              (update :states-created + created)
                              (update :states-deduplicated + deduplicated)
                              (update :branches-pruned + (:skipped outcomes))
                              (update :failure-cache-hits + (:skipped outcomes))
                              (update :max-depth max (inc current-depth))
                              (update :kernel-checks + (count (:results outcomes)))
                              (update :reuse-attempts +
                                      (count (filter #(= :reuse
                                                         (get-in % [:strategy :tactic]))
                                                     (map second (:results outcomes)))))))))))))))))
