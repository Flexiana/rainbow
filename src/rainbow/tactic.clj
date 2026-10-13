(ns rainbow.tactic
  "Untrusted proof-state transformations. Success is always reconstructed by the kernel."
  (:refer-clojure :exclude [apply repeat])
  (:require [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.term :as term]))

(defn- no-goal [state tactic]
  (proof/fail-result state tactic :tactic/no-goal {}))

(defn- focused [state tactic operation]
  (if-let [goal (proof/current-goal state)]
    (operation goal)
    (no-goal state tactic)))

(defn exact [expression]
  (fn [state]
    (focused
     state :exact
     (fn [goal]
       (let [checked (proof/check-in-context (:proof/environment state)
                                             (:goal/context goal)
                                             expression
                                             (:goal/target goal)
                                             (:proof/universes state))]
         (if (= :checked (:status checked))
           (proof/progress state expression []
                           {:event/tactic :exact :event/term expression})
           (proof/fail-result state :exact :tactic/type-mismatch
                              {:term expression :kernel checked})))))))

(defn intro
  ([] (intro nil))
  ([name]
   (fn [state]
     (focused
      state :intro
      (fn [goal]
        (let [raw-target (:goal/target goal)
              target (if (= :pi (first raw-target))
                       raw-target
                       (:term (kernel/normalize (:proof/environment state)
                                                raw-target)))]
          (if-not (= :pi (first target))
            (proof/fail-result state :intro :tactic/target-not-pi
                               {:target (:goal/target goal)})
            (let [id (proof/fresh-goal-id state)
                  domain (second target)
                  body (nth target 2)
                  mode (nth target 3)
                  local {:goal/name (or name (symbol (str "h" (:proof/next-id state))))
                         :goal/type domain
                         :goal/mode mode}
                  next-goal {:goal/id id
                             :goal/context (into [local] (:goal/context goal))
                             :goal/target body
                             :goal/path (conj (:goal/path goal) 0)}]
              (proof/progress state
                              [:lam domain (proof/hole id) mode]
                              [next-goal]
                              {:event/tactic :intro :event/name (:goal/name local)})))))))))

(defn intro-from
  "Introduces a binder from a supplied Pi view of the focused target.

  Search may obtain this view by weak-head unfolding a reducible definition.
  The view must be definitionally equal to the actual goal, and the final proof
  is still reconstructed and checked against the original target."
  ([pi-target] (intro-from pi-target nil))
  ([pi-target name]
   (fn [state]
     (focused
      state :intro
      (fn [goal]
        (let [environment (:proof/environment state)
              raw-target (:goal/target goal)]
          (cond
            (not= :pi (first pi-target))
            (proof/fail-result state :intro :tactic/target-not-pi
                               {:target pi-target})

            (not (true? (kernel/definitionally-equal?
                         environment raw-target pi-target)))
            (proof/fail-result state :intro
                               :tactic/focused-target-mismatch
                               {:target raw-target :focused-target pi-target})

            :else
            (let [id (proof/fresh-goal-id state)
                  domain (second pi-target)
                  body (nth pi-target 2)
                  mode (nth pi-target 3)
                  local {:goal/name
                         (or name (symbol (str "h" (:proof/next-id state))))
                         :goal/type domain
                         :goal/mode mode}
                  next-goal {:goal/id id
                             :goal/context (into [local] (:goal/context goal))
                             :goal/target body
                             :goal/path (conj (:goal/path goal) 0)}]
              (proof/progress
               state [:lam domain (proof/hole id) mode] [next-goal]
               {:event/tactic :intro
                :event/name (:goal/name local)
                :event/focused-target pi-target})))))))))

(defn assumption []
  (fn [state]
    (focused
     state :assumption
     (fn [goal]
       (let [environment (:proof/environment state)
             match (first
                    (keep-indexed
                     (fn [index _local]
                       (let [candidate (term/bound index)
                             checked (proof/check-in-context environment
                                                             (:goal/context goal)
                                                             candidate
                                                             (:goal/target goal)
                                                             (:proof/universes state))]
                         (when (= :checked (:status checked)) candidate)))
                     (:goal/context goal)))]
         (if match
           ((exact match) state)
           (proof/fail-result state :assumption :tactic/no-matching-assumption
                              {:target (:goal/target goal)
                               :context (mapv :goal/type (:goal/context goal))})))))))

(defn- application-spine [expression]
  (loop [current expression
         arguments []]
    (if (= :app (first current))
      (recur (second current) (into [(nth current 2)] arguments))
      [current arguments])))

(defn- apply-arguments [function arguments]
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

(defn reflexivity []
  (fn [state]
    (focused
     state :reflexivity
     (fn [goal]
       (let [environment (:proof/environment state)
             equality-id (environment/resolve-id environment 'equality/Eq)
             reflexivity-id (environment/resolve-id environment 'equality/reflexive)
             [head arguments] (application-spine (beta-head (:goal/target goal)))]
         (if-not (and equality-id reflexivity-id
                      (= :const (first head))
                      (= equality-id (second head))
                      (= 3 (count arguments)))
           (proof/fail-result state :reflexivity :tactic/target-not-equality
                              {:target (:goal/target goal)})
           (let [[carrier left right] arguments]
             (if-not (true? (kernel/definitionally-equal? environment left right carrier))
               (proof/fail-result state :reflexivity :tactic/sides-not-definitionally-equal
                                  {:left left :right right})
               ((exact (-> [:const reflexivity-id (nth head 2)]
                           (term/application carrier)
                           (term/application left)))
                state)))))))))

(defn- replace-subterm
  "Capture-avoiding syntactic replacement of free occurrences."
  [expression from to]
  (letfn [(walk [node depth]
            (let [needle (term/shift from depth)
                  replacement (term/shift to depth)]
              (if (= node needle)
                [replacement 1]
                (case (first node)
                  (:sort :bound :const) [node 0]
                  :app (let [[function function-count] (walk (second node) depth)
                             [argument argument-count] (walk (nth node 2) depth)]
                         [[:app function argument] (+ function-count argument-count)])
                  :lam (let [[domain domain-count] (walk (second node) depth)
                             [body body-count] (walk (nth node 2) (inc depth))]
                         [[:lam domain body (nth node 3)] (+ domain-count body-count)])
                  :pi (let [[domain domain-count] (walk (second node) depth)
                            [body body-count] (walk (nth node 2) (inc depth))]
                        [[:pi domain body (nth node 3)] (+ domain-count body-count)])
                  :let (let [[type type-count] (walk (second node) depth)
                             [value value-count] (walk (nth node 2) depth)
                             [body body-count] (walk (nth node 3) (inc depth))]
                         [[:let type value body]
                          (+ type-count value-count body-count)])))))]
    (walk expression 0)))

(defn rewrite
  ([equality-proof] (rewrite equality-proof {:direction :forward}))
  ([equality-proof {:keys [direction] :or {direction :forward}}]
   (fn [state]
     (focused
      state :rewrite
      (fn [goal]
        (let [environment (:proof/environment state)
              equality-id (environment/resolve-id environment 'equality/Eq)
              symmetric-id (environment/resolve-id environment 'equality/symmetric)
              inferred (proof/infer-in-context environment (:goal/context goal)
                                               equality-proof (:proof/universes state))
              [head arguments] (when (= :checked (:status inferred))
                                 (application-spine (beta-head (:type inferred))))]
          (cond
            (not (contains? #{:forward :backward} direction))
            (proof/fail-result state :rewrite :tactic/invalid-rewrite-direction
                               {:direction direction})

            (not (and equality-id (= :checked (:status inferred))
                      (= :const (first head)) (= equality-id (second head))
                      (= 3 (count arguments))))
            (proof/fail-result state :rewrite :tactic/not-equality-proof
                               {:term equality-proof :inferred inferred})

            :else
            (let [[carrier left right]
                  (mapv (fn [argument]
                          (:term (kernel/normalize environment argument)))
                        arguments)
                  backward? (= :backward direction)
                  evidence (if backward?
                             (-> [:const symmetric-id (nth head 2)]
                                 (term/application carrier)
                                 (term/application left)
                                 (term/application right)
                                 (term/application equality-proof))
                             equality-proof)
                  from (if backward? left right)
                  to (if backward? right left)
                  initial-target (beta-head (:goal/target goal))
                  [initial-rewrite initial-count] (replace-subterm initial-target from to)
                  normalized-target
                  (when (zero? initial-count)
                    (let [[target-head target-arguments] (application-spine initial-target)]
                      (when (and (= :const (first target-head))
                                 (= equality-id (second target-head))
                                 (= 3 (count target-arguments)))
                        (apply-arguments
                         target-head
                         (mapv (fn [argument]
                                 (:term (kernel/normalize environment argument)))
                               target-arguments)))))
                  working-target (or normalized-target initial-target)
                  [new-target occurrence-count]
                  (if (pos? initial-count)
                    [initial-rewrite initial-count]
                    (replace-subterm working-target from to))]
              (if (zero? occurrence-count)
                (proof/fail-result state :rewrite :tactic/no-rewrite-occurrence
                                   {:direction direction :from from
                                    :target working-target})
                (let [id (proof/fresh-goal-id state)
                      shifted-target (term/shift working-target 1)
                      [motive-body motive-count]
                      (replace-subterm shifted-target (term/shift from 1)
                                       [:bound 0])
                      motive [:lam carrier motive-body :explicit]
                      replacement (-> evidence
                                      (term/application motive)
                                      (term/application (proof/hole id)))
                      next-goal {:goal/id id
                                 :goal/context (:goal/context goal)
                                 :goal/target new-target
                                 :goal/path (conj (:goal/path goal) 0)}]
                  (if (zero? motive-count)
                    (proof/fail-result state :rewrite :tactic/motive-construction-failed
                                       {:from from :target working-target})
                    (proof/progress state replacement [next-goal]
                                    {:event/tactic :rewrite
                                     :event/equality equality-proof
                                     :event/direction direction
                                     :event/occurrences occurrence-count}))))))))))))

(defn- recursor-for-block [environment block-id]
  (some (fn [member-id]
          (let [declaration (environment/declaration environment member-id)]
            (when (= :recursor (:rainbow/kind declaration)) declaration)))
        (:block/member-ids (environment/block environment block-id))))

(defn- peel-independent-domains [environment type count]
  (loop [current type
         remaining count
         domains []]
    (if (zero? remaining)
      {:status :ok :domains domains :result current}
      (let [head (if (= :pi (first current))
                   current
                   (:term (kernel/normalize environment current)))]
        (if-not (= :pi (first head))
          {:status :rejected :type current :domains domains}
          (let [body (nth head 2)
                shifted (try
                          (term/shift body -1)
                          (catch clojure.lang.ExceptionInfo _ ::dependent))]
            (if (= ::dependent shifted)
              {:status :dependent :type current :domains domains}
              (recur shifted (dec remaining) (conj domains (second head))))))))))

(defn induction [expression]
  (fn [state]
    (focused
     state :induction
     (fn [goal]
       (let [environment (:proof/environment state)
             context (:goal/context goal)
             universes (:proof/universes state)
             expression-type-result (proof/infer-in-context environment context expression universes)
             expression-type (:type expression-type-result)
             [inductive-head parameters] (when (= :checked (:status expression-type-result))
                                           (application-spine expression-type))
             inductive (when (= :const (first inductive-head))
                         (environment/declaration environment (second inductive-head)))
             recursor (when (= :inductive (:rainbow/kind inductive))
                        (recursor-for-block environment (:rainbow/block-id inductive)))
             goal-type-result (proof/infer-in-context environment context
                                                       (:goal/target goal) universes)
             goal-sort (when (= :checked (:status goal-type-result))
                         (:term (kernel/normalize environment (:type goal-type-result))))]
         (cond
           (not= :checked (:status expression-type-result))
           (proof/fail-result state :induction :tactic/cannot-infer-induction-expression
                              {:expression expression :cause expression-type-result})

           (not= :inductive (:rainbow/kind inductive))
           (proof/fail-result state :induction :tactic/not-inductive
                              {:expression expression :type expression-type})

           (not= :sort (first goal-sort))
           (proof/fail-result state :induction :tactic/goal-not-a-type
                              {:target (:goal/target goal) :cause goal-type-result})

           :else
           (let [shifted-target (term/shift (:goal/target goal) 1)
                 [motive-body _occurrences]
                 (replace-subterm shifted-target (term/shift expression 1) [:bound 0])
                 motive [:lam expression-type motive-body :explicit]
                 recursor-levels (conj (nth inductive-head 2) (second goal-sort))
                 recursor-head [:const (:rainbow/id recursor) recursor-levels]
                 prefix (apply-arguments recursor-head (concat parameters [motive]))
                 prefix-type-result (proof/infer-in-context environment context prefix universes)
                 constructor-count (get-in recursor [:rainbow/recursor :constructor-count])
                 peeled (when (= :checked (:status prefix-type-result))
                          (peel-independent-domains environment
                                                    (:type prefix-type-result)
                                                    constructor-count))]
             (if-not (= :ok (:status peeled))
               (proof/fail-result state :induction :tactic/cannot-build-induction-cases
                                  {:prefix prefix :cause (or peeled prefix-type-result)})
               (let [start (:proof/next-id state)
                     ids (mapv #(str "g-" %)
                               (range start (+ start constructor-count)))
                     case-goals (mapv (fn [id target index]
                                        {:goal/id id
                                         :goal/context context
                                         :goal/target target
                                         :goal/path (conj (:goal/path goal) index)})
                                      ids (:domains peeled) (range))
                     replacement (apply-arguments prefix
                                                  (concat (map proof/hole ids) [expression]))]
                 (proof/progress state replacement case-goals
                                 {:event/tactic :induction
                                  :event/expression expression
                                  :event/cases constructor-count}))))))))))

(defn- independent-application-plan [environment type target]
  (loop [current type
         domains []]
    (if (true? (kernel/definitionally-equal? environment current target))
      {:status :independent :domains domains :result current}
      (let [normalized (:term (kernel/normalize environment current))]
        (cond
          (true? (kernel/definitionally-equal? environment normalized target))
          {:status :independent :domains domains :result normalized}

          (= :pi (first normalized))
          (let [domain (second normalized)
                body (nth normalized 2)
                shifted (try
                          (term/shift body -1)
                          (catch clojure.lang.ExceptionInfo _ ::dependent))]
            (if (= ::dependent shifted)
              {:status :dependent :domains domains :result normalized}
              (recur shifted (conj domains [domain (nth normalized 3)]))))

          :else
          {:status :independent :domains domains :result normalized})))))

(defn apply [expression]
  (fn [state]
    (focused
     state :apply
     (fn [goal]
       (let [environment (:proof/environment state)
             inferred (proof/infer-in-context environment (:goal/context goal) expression
                                              (:proof/universes state))]
         (if-not (= :checked (:status inferred))
           (proof/fail-result state :apply :tactic/cannot-infer
                              {:term expression :kernel inferred})
           (let [{:keys [status domains result]}
                 (independent-application-plan
                  environment (:type inferred) (:goal/target goal))]
             (cond
               (= :dependent status)
               (proof/fail-result state :apply :tactic/dependent-apply-unsupported
                                  {:type (:type inferred)})

               (not (true? (kernel/definitionally-equal? environment result (:goal/target goal))))
               (proof/fail-result state :apply :tactic/conclusion-mismatch
                                  {:candidate-result result :target (:goal/target goal)})

               :else
               (let [start (:proof/next-id state)
                     ids (mapv #(str "g-" %) (range start (+ start (count domains))))
                     goals (mapv (fn [id [domain _mode] index]
                                   {:goal/id id
                                    :goal/context (:goal/context goal)
                                    :goal/target domain
                                    :goal/path (conj (:goal/path goal) index)})
                                 ids domains (range))
                     replacement (reduce (fn [function id]
                                           [:app function (proof/hole id)])
                                         expression ids)]
                 (proof/progress state replacement goals
                                 {:event/tactic :apply
                                  :event/term expression
                                  :event/subgoals (count goals)}))))))))))

(defn- replace-markers [template ids]
  (cond
    (and (vector? template)
         (= :hole (first template))
         (= 2 (count template))
         (integer? (second template)))
    (if-let [id (nth ids (second template) nil)]
      (proof/hole id)
      (throw (ex-info "Refine template names a missing subgoal"
                      {:error/category :tactic/refine-hole-index
                       :index (second template)
                       :subgoals (count ids)})))

    (vector? template) (mapv #(replace-markers % ids) template)
    :else template))

(defn refine
  "Refines the focused hole with an explicit partial core term.
  Template holes are [:hole 0], [:hole 1], ... and targets are explicit core types."
  [template targets]
  (fn [state]
    (focused
     state :refine
     (fn [goal]
       (try
         (let [start (:proof/next-id state)
               ids (mapv #(str "g-" %) (range start (+ start (count targets))))
               replacement (replace-markers template ids)
               goals (mapv (fn [id target index]
                             {:goal/id id
                              :goal/context (:goal/context goal)
                              :goal/target target
                              :goal/path (conj (:goal/path goal) index)})
                           ids targets (range))]
           (proof/progress state replacement goals
                           {:event/tactic :refine
                            :event/template template
                            :event/subgoals (count goals)}))
         (catch clojure.lang.ExceptionInfo exception
           (proof/fail-result state :refine
                              (:error/category (ex-data exception))
                              (ex-data exception))))))))

(defn run [state tactic]
  (tactic state))

(defn then [first-tactic second-tactic]
  (fn [state]
    (let [first-result (run state first-tactic)]
      (if (= :progress (:status first-result))
        (run (:state first-result) second-tactic)
        first-result))))

(defn choice [& tactics]
  (fn [state]
    (loop [remaining tactics
           failures []]
      (if-let [candidate (first remaining)]
        (let [result (run state candidate)]
          (if (contains? #{:progress :proved} (:status result))
            result
            (recur (next remaining) (conj failures (:failure result)))))
        {:status :failure
         :state state
         :failure {:failure/category :tactic/no-choice-succeeded
                   :failure/tactic :choice
                   :failure/detail {:failures failures}}}))))

(defn first-success [tactics]
  (clojure.core/apply choice tactics))

(defn repeat
  ([tactic] (repeat tactic {:max 100}))
  ([tactic {:keys [max] :or {max 100}}]
   (fn [state]
     (loop [current state
            steps 0]
       (if (>= steps max)
         {:status (if (zero? steps) :no-progress :progress)
          :state current
          :steps steps
          :reason :repeat/max-reached}
         (let [result (run current tactic)]
           (case (:status result)
             :proved result
             :progress (recur (:state result) (inc steps))
             {:status (if (zero? steps) :no-progress :progress)
              :state current
              :steps steps
              :last-failure (:failure result)})))))))

(defn- focus-id [state goal-id]
  (let [goals (:proof/goals state)
        selected (first (filter #(= goal-id (:goal/id %)) goals))]
    (when selected
      (assoc state :proof/goals
             (into [selected] (remove #(= goal-id (:goal/id %)) goals))))))

(defn focus [selector tactic]
  (fn [state]
    (let [goals (:proof/goals state)
          selected (cond
                     (string? selector) (some #(when (= selector (:goal/id %)) %) goals)
                     (integer? selector) (nth goals selector nil)
                     (ifn? selector) (some #(when (selector %) %) goals))]
      (if selected
        (run (focus-id state (:goal/id selected)) tactic)
        (proof/fail-result state :focus :tactic/goal-not-found {:selector selector})))))

(defn all-goals [tactic]
  (fn [state]
    (let [original-ids (mapv :goal/id (:proof/goals state))]
      (loop [current state
             remaining original-ids
             progressed? false]
        (if-let [goal-id (first remaining)]
          (if-let [focused-state (focus-id current goal-id)]
            (let [result (run focused-state tactic)]
              (case (:status result)
                :proved result
                :progress (recur (:state result) (next remaining) true)
                result))
            (recur current (next remaining) progressed?))
          {:status (if progressed? :progress :no-progress)
           :state current
           :goals (:proof/goals current)})))))

(defn simplify
  ([equalities] (simplify equalities {:max 100}))
  ([equalities {:keys [max] :or {max 100}}]
   (repeat (clojure.core/apply choice
                               (concat [(reflexivity)]
                                       (map rewrite equalities)))
           {:max max})))

(defn calc [equality-proofs]
  (fn [state]
    (focused
     state :calc
     (fn [goal]
       (if (empty? equality-proofs)
         (proof/fail-result state :calc :tactic/empty-calc {})
         (let [environment (:proof/environment state)
               equality-id (environment/resolve-id environment 'equality/Eq)
               transitive-id (environment/resolve-id environment 'equality/transitive)
               parsed (mapv (fn [expression]
                              (let [inferred (proof/infer-in-context
                                              environment (:goal/context goal) expression
                                              (:proof/universes state))
                                    [head arguments] (when (= :checked (:status inferred))
                                                       (application-spine
                                                        (beta-head (:type inferred))))]
                                {:expression expression :inferred inferred
                                 :head head :arguments arguments}))
                            equality-proofs)]
           (if-not (every? #(and (= :checked (get-in % [:inferred :status]))
                                 (= :const (first (:head %)))
                                 (= equality-id (second (:head %)))
                                 (= 3 (count (:arguments %))))
                           parsed)
             (proof/fail-result state :calc :tactic/calc-step-not-equality
                                {:steps parsed})
             (let [{first-head :head [carrier left first-right] :arguments
                    first-expression :expression} (first parsed)
                   combined
                   (reduce
                    (fn [{:keys [proof right] :as accumulator}
                         {next-head :head [next-carrier next-left next-right] :arguments
                          next-proof :expression}]
                      (if (and (true? (kernel/definitionally-equal?
                                       environment carrier next-carrier nil))
                               (true? (kernel/definitionally-equal?
                                       environment right next-left carrier)))
                        {:proof (-> [:const transitive-id (nth first-head 2)]
                                    (term/application carrier)
                                    (term/application left)
                                    (term/application right)
                                    (term/application next-right)
                                    (term/application proof)
                                    (term/application next-proof))
                         :right next-right}
                        (reduced (assoc accumulator :failure
                                        {:left-right right :next-left next-left
                                         :next-head next-head}))))
                    {:proof first-expression :right first-right}
                    (next parsed))]
               (if-let [failure (:failure combined)]
                 (proof/fail-result state :calc :tactic/calc-endpoint-mismatch failure)
                 (proof/progress state (:proof combined) []
                                 {:event/tactic :calc
                                  :event/steps (count equality-proofs)}))))))))))
