(ns rainbow.kernel
  "Small trusted checker for Rainbow's initial dependent-function calculus."
  (:refer-clojure :exclude [check])
  (:require [clojure.set :as set]
            [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.term :as term]))

;; first/second without allocating a seq (terms and levels are vectors)
(defmacro ^:private fst [x] `(nth ~x 0 nil))
(defmacro ^:private snd [x] `(nth ~x 1 nil))

(def ^:dynamic *reduction-budget* 1000000)
(def ^:dynamic ^:private *normalization-cache* nil)

(defn- reject! [category message data]
  (throw (ex-info message (assoc data :error/category category))))

(defn- consume [fuel operation]
  (if (pos? fuel)
    (dec fuel)
    (reject! :kernel/resource-limit
             "Kernel reduction budget exhausted"
             {:operation operation})))

(defn- unfoldable? [declaration]
  (and (:rainbow/value declaration)
       (contains? #{:reducible :semireducible}
                  (:rainbow/transparency declaration))))

(declare whnf*)

;; ---- natural-number literals ---------------------------------------------------
;; [:nat n] denotes data/succ applied n times to data/zero. No term written before
;; literals existed contains one, so no content id changes. A literal unfolds to a
;; constructor only when a recursor inspects it, and the six reducible definitions
;; below are computed on literals instead of by unary recursion. Each entry is pinned
;; to the content id of the exact definition it computes; rainbow.kernel-native-test
;; compares every entry with the definition's own unary reduction.
(def ^:private nat-id "sha256:3506a443d496ca97e5476cbbb47baadc33ccaef5a3e9717e4bcac7c83acc1453")
(def ^:private zero-term [:const "sha256:11ea4dcb19455ac6d98fa23f4a631c8e72e1d5158d55f35d15a6891da156837a" []])
(def ^:private succ-term [:const "sha256:2c087b95d40cd6088f7ed5b2c005939be25c07dd402f56d99fa9cd076fa760b5" []])
(def ^:private true-term [:const "sha256:0c0f825a7d5e86b6cca9ea42eeae0abde8ff5e3207decf4259ae3687027373df" []])
(def ^:private false-term [:const "sha256:66c0bacea9f97e582fb425ae89bb16134be13945fdb70a42dbbd9a9938b1df10" []])
(def ^:private nat-operations
  {"sha256:ae52ec6e6d33d320ad5cf5bf04a0b7d7a6170f1553ca6921d296cb8f7452b7c5" [2 +']                          ; algebra/nat-add
   "sha256:a30bc2da8bfb2312a7543d07408d4b2e3bfadbd4115c15663abd9d074e829c65" [2 *']                          ; nat/multiply
   "sha256:8b31ca9df8160fd65351654c0599dc50f147c3a5a6593b8fb21ff1ebf9391d5f" [1 #(if (pos? %) (dec' %) 0)]   ; nat/predecessor
   "sha256:939afa870eda7b00fae43fe61c11665d83deb95a70302f36736f84c9d37998d7" [2 #(if (< %1 %2) (-' %2 %1) (-' %1 %2))] ; nat/distance
   "sha256:1a45e6d58cafe9c186133368e8eb7dd1be0244e7409363daa11a1e13898e2ada" [2 ==]                          ; nat/decide-equality
   "sha256:b19fc7e912d5ea4a121499f9a3a32922404045f0fb950f46d115b3764a38d900" [2 <=]})                        ; nat/decide-at-most

(defn- literal-constructor
  "The constructor form a recursor needs: zero, or succ of the predecessor literal."
  [n]
  (if (zero? n) zero-term [:app succ-term [:nat (dec' n)]]))

(defn- application-spine [expression]
  (loop [current expression
         reversed (transient [])]
    (if (= :app (fst current))
      (recur (snd current) (conj! reversed (nth current 2)))
      (let [r (persistent! reversed)]
        [current (if (< (count r) 2) r (vec (rseq r)))]))))

(defn- apply-arguments [function arguments]
  (reduce term/application function arguments))

(defn- nat-value
  "[n fuel] when expression reduces to a closed numeral (a literal or succ ... zero), else nil."
  [environment expression fuel unfolding]
  (loop [expression expression fuel fuel n 0]
    (cond
      ;; numerals written out need no reduction
      (= :nat (fst expression)) [(+' n (snd expression)) fuel]
      (= zero-term expression) [n fuel]
      (and (= :app (fst expression)) (= succ-term (snd expression))) (recur (nth expression 2) fuel (inc' n))
      :else
      (let [[head fuel] (whnf* environment expression fuel unfolding)]
        (cond
          (= :nat (fst head)) [(+' n (snd head)) fuel]
          (= zero-term head) [n fuel]
          (and (= :app (fst head)) (= succ-term (snd head))) (recur (nth head 2) fuel (inc' n))
          :else nil)))))

(defn- native-step
  "Computes a pinned nat operation on literal arguments, or nil to reduce it by unfolding."
  [environment head arguments fuel unfolding]
  (when-let [[arity operation] (and (= :const (fst head)) (get nat-operations (snd head)))]
    ;; Only closed arguments can be numerals to compute with; an open one (a proof
    ;; under binders) is reduced by unfolding, as before, instead of being evaluated
    ;; and given up on at every step.
    (when (and (<= arity (count arguments))
               (every? #(zero? (term/loose-range %)) (subvec arguments 0 arity))
               (= (count (:rainbow/universes (environment/declaration environment (snd head))))
                  (count (nth head 2)))
               (unfoldable? (environment/declaration environment (snd head))))
      ;; The arguments are evaluated on an allowance of their own: unfolding is lazy (it
      ;; may never need an argument), so charging their evaluation to the caller could
      ;; exhaust a budget that unfolding fits in. On any failure the caller unfolds, as
      ;; before, with its fuel untouched; on success it pays one step.
      (when-let [values (try (loop [values [] remaining (seq (subvec arguments 0 arity)) allowance *reduction-budget*]
                               (if-let [argument (fst remaining)]
                                 (when-let [[value allowance] (nat-value environment argument allowance unfolding)]
                                   (recur (conj values value) (rest remaining) allowance))
                                 values))
                             (catch clojure.lang.ExceptionInfo _ nil))]
        (let [result (apply operation values)]
          [(apply-arguments (cond (true? result) true-term (false? result) false-term :else [:nat result])
                            (subvec arguments arity))
           (consume fuel :native)])))))

(defn- recursor-step [environment expression fuel unfolding]
  (let [[head arguments] (application-spine expression)
        declaration (when (= :const (fst head))
                      (environment/declaration environment (snd head)))]
    (when (= :recursor (:rainbow/kind declaration))
      (let [{:keys [parameter-count constructor-count block-id]}
            (:rainbow/recursor declaration)
            target-index (+ parameter-count 1 constructor-count)
            needed (inc target-index)]
        (when (<= needed (count arguments))
          (let [target (nth arguments target-index)
                [target-head remaining] (whnf* environment target fuel unfolding)
                target-head (if (= :nat (fst target-head)) (literal-constructor (snd target-head)) target-head)
                normalized-expression (apply-arguments
                                       head (assoc arguments target-index target-head))
                [constructor-head constructor-arguments]
                (application-spine target-head)
                constructor (when (= :const (fst constructor-head))
                              (environment/declaration environment
                                                       (snd constructor-head)))]
            (if-not (and (= :constructor (:rainbow/kind constructor))
                         (= block-id (:rainbow/block-id constructor)))
              [normalized-expression remaining false]
              (let [{constructor-index :index
                     recursive-fields :recursive-fields
                     field-count :field-count}
                    (:rainbow/constructor constructor)
                    field-arguments (let [from (min parameter-count (count constructor-arguments))]
                                      (subvec constructor-arguments from
                                              (min (count constructor-arguments) (+ from field-count))))
                    _ (when-not (= field-count (count field-arguments))
                        (reject! :kernel/malformed-constructor-application
                                 "Constructor has too few field arguments"
                                 {:constructor (:rainbow/id constructor)
                                  :expected field-count
                                  :actual (count field-arguments)}))
                    case-term (nth arguments (+ parameter-count 1 constructor-index))
                    prefix (subvec arguments 0 (+ parameter-count 1 constructor-count))
                    reduced (reduce (fn [result [field recursive?]]
                                      (let [with-field (term/application result field)]
                                        (if recursive?
                                          (term/application
                                           with-field
                                           (apply-arguments head (conj prefix field)))
                                          with-field)))
                                    case-term
                                    (map vector field-arguments recursive-fields))
                    with-extra (apply-arguments reduced (subvec arguments needed))]
                [with-extra (consume remaining :iota) true]))))))))

(defn- whnf*
  [environment expression fuel unfolding]
  (case (fst expression)
    :let (recur environment
                (term/instantiate (nth expression 3) (nth expression 2))
                (consume fuel :zeta)
                unfolding)

    :const (let [id (snd expression)
                 declaration (environment/declaration environment id)]
             (when-not declaration
               (reject! :kernel/unknown-constant "Unknown constant" {:constant/id id}))
             (if (unfoldable? declaration)
               (do
                 (when (contains? unfolding id)
                   (reject! :kernel/cyclic-reduction
                            "Cyclic transparent definition"
                            {:constant/id id :unfolding unfolding}))
                 (let [parameters (:rainbow/universes declaration)
                       arguments (nth expression 2)]
                   (when-not (= (count parameters) (count arguments))
                     (reject! :kernel/universe-arity
                              "Wrong number of universe arguments"
                              {:constant/id id
                               :expected (count parameters)
                               :actual (count arguments)}))
                   (recur environment
                          (term/instantiate-universes
                           (:rainbow/value declaration)
                           (zipmap parameters arguments))
                          (consume fuel :delta)
                          (conj unfolding id))))
               [expression fuel]))

    :app (if-let [[computed remaining] (let [[head arguments] (application-spine expression)]
                                         (native-step environment head arguments fuel unfolding))]
           (recur environment computed remaining unfolding)
         (let [[function remaining] (whnf* environment (snd expression) fuel unfolding)]
           (if (= :lam (fst function))
             (recur environment
                    (term/instantiate (nth function 2) (nth expression 2))
                    (consume remaining :beta)
                    unfolding)
             (let [rebuilt [:app function (nth expression 2)]
                   step (recursor-step environment rebuilt remaining unfolding)]
               (if step
                 (let [[next-expression next-fuel reduced?] step]
                   (if reduced?
                     (recur environment next-expression next-fuel unfolding)
                     [next-expression next-fuel]))
                 [rebuilt remaining])))))

    [expression fuel]))

(declare normalize*)

(defn- normalize-uncached*
  [environment expression fuel]
  (let [[head fuel] (whnf* environment expression fuel #{})]
    (case (fst head)
      :sort [[:sort (term/normalize-level (snd head))] fuel]
      (:bound :nat) [head fuel]
      :const [(if (= zero-term head) [:nat 0] head) fuel]
      :app (let [[function fuel] (normalize* environment (snd head) fuel)
                 [argument fuel] (normalize* environment (nth head 2) fuel)]
             [(if (and (= succ-term function) (= :nat (fst argument)))
                [:nat (inc' (snd argument))]
                [:app function argument])
              fuel])
      :lam (let [[domain fuel] (normalize* environment (snd head) fuel)
                 [body fuel] (normalize* environment (nth head 2) fuel)
                 candidate [:lam domain body (nth head 3)]]
             ;; Supported eta: (fn [x] (f x)) = f when x is not free in f.
             (if (and (= :app (fst body))
                      (= [:bound 0] (nth body 2)))
               (try
                 [(term/shift (snd body) -1) (consume fuel :eta)]
                 (catch clojure.lang.ExceptionInfo _ [candidate fuel]))
               [candidate fuel]))
      :pi (let [[domain fuel] (normalize* environment (snd head) fuel)
                [body fuel] (normalize* environment (nth head 2) fuel)]
            [[:pi domain body (nth head 3)] fuel])
      :let (throw (AssertionError. "whnf must eliminate lets")))))

(defn- normalize*
  [environment expression fuel]
  (if-let [entry (and *normalization-cache*
                      (find @*normalization-cache* expression))]
    [(val entry) fuel]
    (let [[normal remaining] (normalize-uncached* environment expression fuel)]
      (when *normalization-cache*
        (swap! *normalization-cache* assoc expression normal))
      [normal remaining])))

(defn- unary [expression nodes]
  (case (fst expression)
    :nat (let [n (snd expression)]
           (when (> n @nodes)
             (reject! :kernel/resource-limit "Unary numeral output budget exhausted"
                      {:operation :unary-output :required n :remaining @nodes}))
           (vswap! nodes - n)
           (loop [remaining n result zero-term]
             (if (zero? remaining) result
                 (recur (dec' remaining) [:app succ-term result]))))
    :app [:app (unary (snd expression) nodes) (unary (nth expression 2) nodes)]
    (:lam :pi) [(fst expression) (unary (snd expression) nodes) (unary (nth expression 2) nodes) (nth expression 3)]
    :let [:let (unary (snd expression) nodes) (unary (nth expression 2) nodes) (unary (nth expression 3) nodes)]
    expression))

(defn normalize
  "Normalizes a term. :max-unary-nodes bounds generated successor nodes across
  the returned term (default 1000000), independently of the reduction budget."
  ([environment expression] (normalize environment expression nil))
  ([environment expression options]
   (try
     (term/assert-term! expression)
     (let [budget (get options :reductions *reduction-budget*)
           cache (or *normalization-cache* (atom {}))
           [normal remaining]
           (binding [*normalization-cache* cache]
             (normalize* environment expression budget))]
       ;; Literals are internal: callers get the unary numerals they always got.
       {:status :normalized :term (if (::literals options) normal
                                   (unary normal (volatile! (get options :max-unary-nodes 1000000))))
        :reductions (- budget remaining)})
     (catch clojure.lang.ExceptionInfo exception
       {:status (if (= :kernel/resource-limit (:error/category (ex-data exception)))
                  :resource-limit
                  :rejected)
        :error (ex-data exception)
        :message (ex-message exception)}))))

(defn- normal-form! [environment expression]
  (let [result (normalize environment expression {:reductions *reduction-budget* ::literals true})]
    (if (= :normalized (:status result))
      (:term result)
      (reject! (get-in result [:error :error/category])
               (:message result)
               (:error result)))))

;; ---- lazy conversion ------------------------------------------------------------
;; Before normalising both sides completely, try to show them equal lazily: reduce each
;; head without unfolding definitions (beta, zeta, iota, the pinned nat operations),
;; compare equal heads argument by argument, and otherwise unfold one head definition
;; and try again. Every step is a conversion rule the full procedure also uses (the
;; reductions are this kernel's own; congruence holds for definitional equality), so a
;; lazy success is a pair whose normal forms are equal. A lazy failure decides nothing:
;; the full procedure below runs as before. Binder modes and constant universe
;; arguments must match exactly, as they must in normal forms.
(def ^:dynamic ^:private *lazy-fuel* nil)
(def ^:dynamic ^:private *lazy-failed* nil)

(defn- lazy-step! []
  (when (neg? (vswap! *lazy-fuel* dec))
    (throw (ex-info "Lazy conversion budget exhausted" {::lazy-exhausted true}))))

(defn- whnf-core
  "Head reduction without unfolding a definition at the head."
  [environment expression]
  (loop [expression expression]
    (case (fst expression)
      :let (do (lazy-step!) (recur (term/instantiate (nth expression 3) (nth expression 2))))
      :app (let [[head arguments] (application-spine expression)]
             (if-let [[computed _] (native-step environment head arguments *reduction-budget* #{})]
               (do (lazy-step!) (recur computed))
               (if (= :lam (fst head))
                 (do (lazy-step!)
                     (recur (apply-arguments (term/instantiate (nth head 2) (first arguments)) (subvec arguments 1))))
                 (if-let [[next-expression _ reduced?] (recursor-step environment expression *reduction-budget* #{})]
                   (if reduced? (do (lazy-step!) (recur next-expression)) next-expression)
                   expression))))
      expression)))

(defn- unfold-head
  "The expression with its head definition unfolded once, or nil when the head is not one."
  [environment expression]
  (let [[head arguments] (application-spine expression)]
    (when (= :const (fst head))
      (let [declaration (environment/declaration environment (snd head))]
        (when (and (unfoldable? declaration)
                   (= (count (:rainbow/universes declaration)) (count (nth head 2))))
          (lazy-step!)
          [(snd head)
           (apply-arguments (term/instantiate-universes (:rainbow/value declaration)
                                                        (zipmap (:rainbow/universes declaration) (nth head 2)))
                            arguments)])))))

(declare lazy-equal?)

(defn- congruent? [environment left right]
  (let [tag (fst left)]
    (cond
      (not= tag (fst right)) false
      (= :sort tag) (= (term/normalize-level (snd left)) (term/normalize-level (snd right)))
      (#{:lam :pi} tag) (and (= (nth left 3) (nth right 3))
                             (lazy-equal? environment (snd left) (snd right))
                             (lazy-equal? environment (nth left 2) (nth right 2)))
      (= :app tag) (let [[left-head left-arguments] (application-spine left)
                         [right-head right-arguments] (application-spine right)]
                     (and (= left-head right-head)
                          (= (count left-arguments) (count right-arguments))
                          (every? true? (map #(lazy-equal? environment %1 %2) left-arguments right-arguments))))
      :else false)))

(defn- depends-on? [environment id other]
  (contains? (set (:rainbow/dependencies (environment/declaration environment id))) other))

(defn- lazy-equal? [environment left right]
  (cond
    (= left right) true
    (contains? @*lazy-failed* [left right]) false
    :else
    (do
      (lazy-step!)
      (let [left (whnf-core environment left)
            right (whnf-core environment right)]
        (or (= left right)
            (congruent? environment left right)
            (let [[left-id left-unfolded] (unfold-head environment left)
                  [right-id right-unfolded] (unfold-head environment right)]
              (cond
                (and left-unfolded right-unfolded)
                (cond (= left-id right-id) (lazy-equal? environment left-unfolded right-unfolded)
                      (depends-on? environment right-id left-id) (lazy-equal? environment left right-unfolded)
                      (depends-on? environment left-id right-id) (lazy-equal? environment left-unfolded right)
                      :else (lazy-equal? environment left-unfolded right-unfolded))
                left-unfolded (lazy-equal? environment left-unfolded right)
                right-unfolded (lazy-equal? environment left right-unfolded)
                :else false))
            (do (vswap! *lazy-failed* conj [left right]) false))))))

(defn- lazily-equal? [environment left right]
  (binding [*lazy-fuel* (volatile! *reduction-budget*)
            *lazy-failed* (volatile! #{})]
    (try
      (true? (lazy-equal? environment left right))
      ;; any failure (budget, a rejection, the host stack) leaves the decision to the full procedure
      (catch clojure.lang.ExceptionInfo _ false)
      (catch StackOverflowError _ false))))

(defn- definitionally-equal!* [environment left right]
  ;; Keep the original decision procedure. Untyped congruence/eta shortcuts can
  ;; erase binder annotations or bypass rejection inside a shared subterm.
  ;; Normal forms are compared up to level equivalence: a level is equal to another with the
  ;; same value under every assignment (term/level-equivalent?).
  (or (= left right)
      (binding [*normalization-cache* (atom {})]
        (let [left (normal-form! environment left)
              right (normal-form! environment right)]
          (or (= left right) (term/equivalent-up-to-levels? left right))))))

(defn- convertible!*
  "Type checking's conversion test: the lazy attempt, then the original procedure.
  Used only where one side is the inferred type of a checked term (and the other a
  checked expected type, or a binder domain that is itself checked next), so no
  rejection inside a shared subterm can be bypassed: a well-typed side contains no
  unknown constant and no malformed recursor application, and the lazy path never
  equates such a subterm with anything else. The public definitionally-equal? keeps
  the original procedure exactly."
  [environment left right]
  (or (= left right)
      (lazily-equal? environment left right)
      (definitionally-equal!* environment left right)))

(defn definitionally-equal?
  ([environment left right] (definitionally-equal? environment left right nil))
  ([environment left right _type]
   (try
     (term/assert-term! left)
     (term/assert-term! right)
     (definitionally-equal!* environment left right)
     (catch clojure.lang.ExceptionInfo exception
       (if (= :kernel/resource-limit (:error/category (ex-data exception)))
         {:status :resource-limit :error (ex-data exception)}
         false)))))

(defn- assert-level-scope! [level universe-parameters]
  (let [unknown (set/difference (term/level-params level) universe-parameters)]
    (when (seq unknown)
      (reject! :kernel/unbound-universe
               "Universe parameter is not declared"
               {:unknown unknown :allowed universe-parameters}))))

(defn- assert-term-level-scope! [expression universe-parameters]
  (case (fst expression)
    :sort (assert-level-scope! (snd expression) universe-parameters)
    (:bound :nat) nil
    :const (doseq [level (nth expression 2)]
             (assert-level-scope! level universe-parameters))
    :app (do (assert-term-level-scope! (snd expression) universe-parameters)
             (assert-term-level-scope! (nth expression 2) universe-parameters))
    (:lam :pi) (do (assert-term-level-scope! (snd expression) universe-parameters)
                   (assert-term-level-scope! (nth expression 2) universe-parameters))
    :let (do (assert-term-level-scope! (snd expression) universe-parameters)
             (assert-term-level-scope! (nth expression 2) universe-parameters)
             (assert-term-level-scope! (nth expression 3) universe-parameters))))

(declare infer*)

(defn- sort-level! [environment type]
  (let [head (fst (whnf* environment type *reduction-budget* #{}))]
    (if (= :sort (fst head))
      (snd head)
      (reject! :kernel/expected-sort
               "Expected a type whose type is a sort"
               {:actual type :actual-normal head}))))

(defn- check* [environment context expression expected]
  (if (and (= :lam (fst expression))
           (= :pi (fst (fst (whnf* environment expected
                                        *reduction-budget* #{})))))
    (let [expected-pi (fst (whnf* environment expected *reduction-budget* #{}))
          actual-domain (snd expression)
          expected-domain (snd expected-pi)]
      (when-not (= (nth expression 3) (nth expected-pi 3))
        (reject! :kernel/binder-mode-mismatch
                 "Lambda binder mode differs from expected Pi binder"
                 {:expected (nth expected-pi 3) :actual (nth expression 3)}))
      (when-not (convertible!* environment actual-domain expected-domain)
        (reject! :kernel/type-mismatch
                 "Lambda domain does not match expected Pi domain"
                 {:expected expected-domain :actual actual-domain}))
      (sort-level! environment (infer* environment context actual-domain))
      (check* environment
              (into [actual-domain] context)
              (nth expression 2)
              (nth expected-pi 2)))
    (let [actual (infer* environment context expression)]
      (when-not (convertible!* environment actual expected)
        (reject! :kernel/type-mismatch
                 "Term does not inhabit expected type"
                 {:expected expected :actual actual :term expression}))))
  expression)

;; Large elimination from Prop. A recursor of an inductive type with two or more constructors may
;; eliminate into a universe above Prop only when the type is not a proposition: at Prop, proofs are
;; meant to be indistinguishable (the opt-in proof-irrelevance axiom says so), and eliminating Sum P Q
;; into Bool would tell inl from inr, deriving False. A single-constructor type is fine: its fields are
;; then propositions too (constructor fields live at most at the type's own sort).
;; A use whose level is fixed is decided at once; a universe-polymorphic use (data/List.rec at Sort u)
;; records the requirement "level >= 1" on the declaration using it (:rainbow/level-requirements, not
;; part of any content id), and every use of that declaration must keep it.
(def ^:private one-level [:succ [:zero]])

(defn- level-at-most-terms [level upper?]
  (case (fst level)
    :zero [[nil 0]]
    :param [[(snd level) 0]]
    :succ (mapv (fn [[base k]] [base (inc k)]) (level-at-most-terms (snd level) upper?))
    :max (into (level-at-most-terms (snd level) upper?) (level-at-most-terms (nth level 2) upper?))
    :imax (if upper?
            (into (level-at-most-terms (snd level) upper?) (level-at-most-terms (nth level 2) upper?))
            (level-at-most-terms (nth level 2) upper?))))

(defn- level-at-most*? [a b]
  (let [bs (level-at-most-terms (term/normalize-level b) false)]
    (every? (fn [[base k]]
              (some (fn [[base' k']] (and (or (nil? base) (= base base')) (<= k k'))) bs))
            (level-at-most-terms (term/normalize-level a) true))))

(defn- elimination-requirements
  "Levels that must be at least 1 for this use of a declaration at the given universe levels."
  [environment declaration levels]
  (let [parameters (:rainbow/universes declaration)
        substitution (zipmap parameters levels)
        inherited (map #(term/instantiate-level % substitution) (:rainbow/level-requirements declaration))
        recursor (:rainbow/recursor declaration)]
    (if (and recursor (<= 2 (:constructor-count recursor))
             (not (level-at-most*? (last levels) [:zero])))
      (let [block (environment/block environment (:block-id recursor))
            sort-level (get-in block [:block/spec :block/sort-level])
            block-universes (get-in block [:block/spec :block/universes])]
        (conj (vec inherited)
              (term/instantiate-level sort-level (zipmap block-universes (butlast levels)))))
      inherited)))

(defn- assert-level-requirements! [environment declaration levels]
  (doseq [level (elimination-requirements environment declaration levels)]
    (when (level-at-most*? level [:zero])
      (reject! :kernel/large-elimination-from-prop
               "Large elimination from a proposition with several constructors"
               {:constant/id (:rainbow/id declaration) :levels levels :required-nonzero level}))))

(defn- term-level-requirements
  "The requirements a term's constant uses leave open (not already at least 1)."
  [environment expression]
  (letfn [(walk [acc node]
            (case (fst node)
              :const (let [declaration (environment/declaration environment (snd node))]
                       (into acc (remove #(level-at-most*? one-level %))
                             (when declaration (elimination-requirements environment declaration (nth node 2)))))
              :app (walk (walk acc (snd node)) (nth node 2))
              (:lam :pi) (walk (walk acc (snd node)) (nth node 2))
              :let (walk (walk (walk acc (snd node)) (nth node 2)) (nth node 3))
              acc))]
    (into #{} (map term/normalize-level) (walk #{} expression))))

(defn- infer-constant [environment id levels]
  (let [declaration (environment/declaration environment id)]
    (when-not declaration
      (reject! :kernel/unknown-constant "Unknown constant" {:constant/id id}))
    (let [parameters (:rainbow/universes declaration)]
      (when-not (= (count parameters) (count levels))
        (reject! :kernel/universe-arity
                 "Wrong number of universe arguments"
                 {:constant/id id :expected (count parameters) :actual (count levels)}))
      (assert-level-requirements! environment declaration levels)
      (term/instantiate-universes (:rainbow/type declaration)
                                  (zipmap parameters levels)))))

(defn- infer* [environment context expression]
  (case (fst expression)
    :sort [:sort [:succ (snd expression)]]

    :bound (let [index (snd expression)]
             (when-not (< index (count context))
               (reject! :kernel/unbound-variable
                        "de Bruijn index is outside the local context"
                        {:index index :context-size (count context)}))
             (term/shift (nth context index) (inc index)))

    :const (infer-constant environment (snd expression) (nth expression 2))

    :nat (do (infer-constant environment nat-id []) [:const nat-id []])

    :app (let [function-type (infer* environment context (snd expression))
               function-head (fst (whnf* environment function-type
                                            *reduction-budget* #{}))]
           (when-not (= :pi (fst function-head))
             (reject! :kernel/not-a-function
                      "Application function does not have a Pi type"
                      {:function (snd expression) :type function-type}))
           (check* environment context (nth expression 2) (snd function-head))
           (term/instantiate (nth function-head 2) (nth expression 2)))

    :lam (let [domain (snd expression)
               _ (sort-level! environment (infer* environment context domain))
               body-type (infer* environment (into [domain] context) (nth expression 2))]
           [:pi domain body-type (nth expression 3)])

    :pi (let [domain (snd expression)
              domain-sort (infer* environment context domain)
              domain-level (sort-level! environment domain-sort)
              body-sort (infer* environment (into [domain] context) (nth expression 2))
              body-level (sort-level! environment body-sort)]
          [:sort (term/normalize-level [:imax domain-level body-level])])

    :let (let [declared-type (snd expression)
               _ (sort-level! environment (infer* environment context declared-type))
               _ (check* environment context (nth expression 2) declared-type)
               body-type (infer* environment (into [declared-type] context) (nth expression 3))]
           (term/instantiate body-type (nth expression 2)))))

(defn infer
  ([environment expression] (infer environment expression #{}))
  ([environment expression universe-parameters]
   (try
     (term/assert-term! expression)
     (assert-term-level-scope! expression (set universe-parameters))
     {:status :checked
      :term expression
      :type (infer* environment [] expression)}
     (catch clojure.lang.ExceptionInfo exception
       {:status :rejected
        :error (ex-data exception)
        :message (ex-message exception)}))))

(defn check
  ([environment expression expected] (check environment expression expected #{}))
  ([environment expression expected universe-parameters]
   (try
     (term/assert-term! expression)
     (term/assert-term! expected)
     (assert-term-level-scope! expression (set universe-parameters))
     (assert-term-level-scope! expected (set universe-parameters))
     (sort-level! environment (infer* environment [] expected))
     (check* environment [] expression expected)
     {:status :checked :term expression :type expected}
     (catch clojure.lang.ExceptionInfo exception
       {:status :rejected
        :error (ex-data exception)
        :message (ex-message exception)}))))

(defn- declaration-axioms [environment declaration]
  (reduce
   (fn [axioms dependency-id]
     (let [dependency (environment/declaration environment dependency-id)]
       (cond
         (= :axiom (:rainbow/kind dependency)) (conj axioms dependency-id)
         dependency (into axioms (:rainbow/axioms dependency))
         :else axioms)))
   #{}
   (:rainbow/dependencies declaration)))

(defn- validate-declaration! [environment declaration]
  (let [kind (:rainbow/kind declaration)
        universes (:rainbow/universes declaration)
        type (:rainbow/type declaration)
        value (:rainbow/value declaration)]
    (when-not (contains? #{:definition :theorem :axiom} kind)
      (reject! :kernel/unsupported-declaration-kind
               "Unsupported declaration kind in the V0 kernel"
               {:kind kind}))
    (when-not (and (vector? universes)
                   (every? symbol? universes)
                   (= (count universes) (count (distinct universes))))
      (reject! :kernel/invalid-universe-parameters
               "Universe parameters must be a vector of distinct symbols"
               {:universes universes}))
    (term/assert-term! type)
    (when-not (term/closed? type)
      (reject! :kernel/free-variable "Declaration type is not closed" {:term type}))
    (let [type-result (infer environment type (set universes))]
      (when-not (= :checked (:status type-result))
        (reject! :kernel/invalid-declaration-type
                 "Declaration type is not a well-formed type"
                 {:cause type-result}))
      (try
        (sort-level! environment (:type type-result))
        (catch clojure.lang.ExceptionInfo exception
          (reject! :kernel/invalid-declaration-type
                   "Declaration type does not itself inhabit a sort"
                   {:cause (ex-data exception)}))))
    (if (= :axiom kind)
      (when (some? value)
        (reject! :kernel/axiom-has-value "An axiom cannot have a value" {}))
      (do
        (when-not value
          (reject! :kernel/missing-value "Definition or theorem is missing a value" {:kind kind}))
        (term/assert-term! value)
        (when-not (term/closed? value)
          (reject! :kernel/free-variable "Declaration value is not closed" {:term value}))
        (let [check-result (check environment value type (set universes))]
          (when-not (= :checked (:status check-result))
            (reject! :kernel/invalid-declaration-value
                     "Declaration value does not inhabit its type"
                     {:cause check-result})))))
    (let [actual-dependencies (into (term/constants type)
                                    (if value (term/constants value) #{}))]
      (when-not (= actual-dependencies (:rainbow/dependencies declaration))
        (reject! :kernel/dependency-mismatch
                 "Declared dependencies differ from term dependencies"
                 {:declared (:rainbow/dependencies declaration)
                  :actual actual-dependencies})))
    declaration))

(defn add-declaration
  "Validates a declaration and returns {:status :accepted :environment ... :declaration ...}.
  No mutable registry is consulted or changed."
  [environment candidate]
  (try
    (when (:rainbow/block-id candidate)
      (reject! :kernel/standalone-block-member
               "Inductive block members must be added atomically" {}))
    (when-not (= environment/schema-version
                 (:rainbow.environment/schema-version environment))
      (reject! :kernel/environment-schema "Unsupported environment schema" {}))
    (let [base (merge {:rainbow/universes []
                       :rainbow/value nil
                       :rainbow/transparency :opaque
                       :rainbow/dependencies #{}
                       :rainbow/aliases #{}
                       :rainbow/schema-version 1}
                      candidate)
          _ (when-not (= 1 (:rainbow/schema-version base))
              (reject! :kernel/declaration-schema "Unsupported declaration schema"
                       {:actual (:rainbow/schema-version base)}))
          _ (when-not (and (set? (:rainbow/aliases base))
                           (every? symbol? (:rainbow/aliases base)))
              (reject! :kernel/invalid-aliases "Aliases must be a set of symbols"
                       {:aliases (:rainbow/aliases base)}))
          _ (when-not (contains? #{:reducible :semireducible :opaque}
                                 (:rainbow/transparency base))
              (reject! :kernel/invalid-transparency "Invalid declaration transparency"
                       {:transparency (:rainbow/transparency base)}))
          _ (validate-declaration! environment base)
          axioms (declaration-axioms environment base)
          semantic (assoc base :rainbow/axioms axioms)
          computed-id (environment/declaration-id semantic)
          supplied-id (:rainbow/id candidate)
          _ (when (and supplied-id (not= supplied-id computed-id))
              (reject! :kernel/forged-declaration-id
                       "Supplied declaration ID does not match semantic content"
                       {:supplied supplied-id :computed computed-id}))
          checked (assoc semantic :rainbow/id computed-id)
          requirements (into (term-level-requirements environment (:rainbow/type base))
                             (when (:rainbow/value base) (term-level-requirements environment (:rainbow/value base))))
          checked (cond-> checked (seq requirements) (assoc :rainbow/level-requirements requirements))
          existing (environment/declaration environment computed-id)
          aliases (into (or (:rainbow/aliases existing) #{}) (:rainbow/aliases checked))
          checked (assoc checked :rainbow/aliases aliases)
          alias-conflict (some (fn [alias]
                                 (when-let [old (get-in environment [:rainbow.environment/aliases alias])]
                                   (when (not= old computed-id) [alias old])))
                               aliases)]
      (when alias-conflict
        (reject! :kernel/alias-conflict "Alias already identifies another declaration"
                 {:alias (fst alias-conflict) :existing-id (snd alias-conflict)}))
      {:status :accepted
       :declaration checked
       :environment (-> environment
                        (assoc-in [:rainbow.environment/declarations computed-id] checked)
                        (update :rainbow.environment/aliases
                                into (zipmap aliases (repeat computed-id)))
                        (cond-> (nil? existing)
                          (update :rainbow.environment/order conj computed-id)))})
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected
       :error (ex-data exception)
       :message (ex-message exception)})))

(def motive-universe-parameter '_rainbow_motive_universe)

(defn- contains-self? [value]
  (cond
    (= [:self] value) true
    (coll? value) (boolean (some contains-self? value))
    :else false))

(defn- normalize-block-level [level universe-index]
  (case (fst level)
    :zero [:zero]
    :param (if-some [index (get universe-index (snd level))]
             [:parameter index]
             (reject! :kernel/unbound-universe "Block level uses an undeclared universe"
                      {:level level}))
    :succ [:succ (normalize-block-level (snd level) universe-index)]
    :max [:max (normalize-block-level (snd level) universe-index)
          (normalize-block-level (nth level 2) universe-index)]
    :imax [:imax (normalize-block-level (snd level) universe-index)
           (normalize-block-level (nth level 2) universe-index)]))

(defn- validate-block-type-ast!
  "Checks the small named AST used by inductive descriptors before it is
  compiled to de Bruijn core terms. `known` contains parameters and earlier
  constructor fields, so dependent references cannot point forward."
  [ast known universe-parameters]
  (when-not (vector? ast)
    (reject! :kernel/malformed-block-type "Inductive type AST must be a vector"
             {:ast ast}))
  (case (fst ast)
    :var
    (when-not (and (= 2 (count ast)) (symbol? (snd ast))
                   (contains? known (snd ast)))
      (reject! :kernel/unknown-block-variable
               "Inductive type references an unknown or forward variable"
               {:ast ast :known known}))

    :sort
    (do
      (when-not (and (= 2 (count ast)) (term/level? (snd ast)))
        (reject! :kernel/malformed-block-type "Malformed sort in inductive type"
                 {:ast ast}))
      (assert-level-scope! (snd ast) universe-parameters))

    :const
    (do
      (when-not (and (= 3 (count ast))
                     (or (string? (snd ast)) (symbol? (snd ast)))
                     (vector? (nth ast 2))
                     (every? term/level? (nth ast 2)))
        (reject! :kernel/malformed-block-type
                 "Malformed constant in inductive type" {:ast ast}))
      (doseq [level (nth ast 2)]
        (assert-level-scope! level universe-parameters)))

    :app
    (do
      (when (< (count ast) 3)
        (reject! :kernel/malformed-block-type
                 "Inductive type application needs an argument" {:ast ast}))
      (doseq [node (rest ast)]
        (validate-block-type-ast! node known universe-parameters)))

    :pi
    (let [[_ bindings body] ast]
      (when-not (and (= 3 (count ast)) (vector? bindings)
                     (every? #(and (vector? %) (= 2 (count %))
                                   (symbol? (fst %)))
                             bindings))
        (reject! :kernel/malformed-block-type
                 "Malformed dependent function in inductive type" {:ast ast}))
      (loop [scope known remaining bindings]
        (if-let [[name type-ast] (fst remaining)]
          (do (validate-block-type-ast! type-ast scope universe-parameters)
              (recur (conj scope name) (next remaining)))
          (validate-block-type-ast! body scope universe-parameters))))

    (reject! :kernel/malformed-block-type
             "Unsupported node in inductive type AST" {:ast ast}))
  ast)

(defn- normalize-block-type-ast
  ([ast universe-index known] (normalize-block-type-ast ast universe-index known 0))
  ([ast universe-index known depth]
   (case (fst ast)
     :var (or (get known (snd ast))
              (reject! :kernel/unknown-block-variable
                       "Unknown variable while normalizing inductive type"
                       {:ast ast :known (keys known)}))
     :sort [:sort (normalize-block-level (snd ast) universe-index)]
     :const [:const (snd ast)
             (mapv #(normalize-block-level % universe-index) (nth ast 2))]
     :app (into [:app (normalize-block-type-ast (snd ast) universe-index known depth)]
                (map #(normalize-block-type-ast % universe-index known depth) (drop 2 ast)))
     :pi (let [[_ bindings body] ast]
           ;; Absolute binder positions must continue across nested Pis. Resetting
           ;; to zero aliases outer and inner variables in the content identity.
           (loop [scope known index depth remaining bindings normalized []]
             (if-let [[name type-ast] (fst remaining)]
               (recur (assoc scope name [:bound index])
                      (inc index) (next remaining)
                      (conj normalized
                            (normalize-block-type-ast type-ast universe-index scope index)))
               [:pi normalized
                (normalize-block-type-ast body universe-index scope index)])))
     :self [:self])))

(defn- validate-block-spec! [spec]
  (let [universes (:block/universes spec)
        parameters (:block/parameters spec)
        constructors (:block/constructors spec)
        parameter-names (mapv :parameter/name parameters)
        aliases (into [(:block/alias spec)] (map :constructor/alias constructors))]
    (when-not (= 1 (:block/schema-version spec))
      (reject! :kernel/inductive-schema "Unsupported inductive block schema"
               {:actual (:block/schema-version spec)}))
    (when-not (and (symbol? (:block/alias spec))
                   (vector? universes) (every? symbol? universes)
                   (= (count universes) (count (distinct universes)))
                   (not (some #{motive-universe-parameter} universes)))
      (reject! :kernel/invalid-inductive-header "Malformed inductive block header"
               {:alias (:block/alias spec) :universes universes}))
    (when-not (and (vector? parameters)
                   (every? #(and (symbol? (:parameter/name %))
                                 (vector? (:parameter/type %)))
                           parameters)
                   (= (count parameter-names) (count (distinct parameter-names))))
      (reject! :kernel/invalid-inductive-parameters
               "Inductive parameters must have distinct names and type ASTs"
               {:parameters parameters}))
    (loop [known #{} remaining parameters]
      (when-let [{:parameter/keys [name type]} (fst remaining)]
        (validate-block-type-ast! type known (set universes))
        (recur (conj known name) (next remaining))))
    (when-not (and (term/level? (:block/sort-level spec))
                   (seq constructors)
                   (vector? constructors))
      (reject! :kernel/invalid-inductive-result "Malformed inductive result or constructors"
               {:sort-level (:block/sort-level spec)}))
    (assert-level-scope! (:block/sort-level spec) (set universes))
    (when-not (and (every? symbol? aliases)
                   (= (count aliases) (count (distinct aliases))))
      (reject! :kernel/inductive-alias-conflict
               "Inductive and constructor aliases must be distinct symbols"
               {:aliases aliases}))
    (doseq [[constructor-index constructor] (map-indexed vector constructors)]
      (let [fields (:constructor/fields constructor)
            field-names (mapv :field/name fields)]
        (when-not (and (vector? fields)
                       (every? symbol? field-names)
                       (= (count field-names) (count (distinct field-names)))
                       (empty? (set/intersection (set parameter-names) (set field-names))))
          (reject! :kernel/invalid-constructor-fields
                   "Constructor fields must have distinct non-shadowing names"
                   {:constructor constructor-index :fields fields}))
        (loop [known (set parameter-names)
               remaining fields]
          (when-let [field (fst remaining)]
            (let [field-type (:field/type field)]
              (cond
                (= [:self] field-type) nil
                (contains-self? field-type)
                (reject! :kernel/non-strictly-positive
                         "Recursive occurrence must be an entire constructor field"
                         {:constructor constructor-index :field field})
                :else (validate-block-type-ast! field-type known
                                                (set universes))))
            (recur (conj known (:field/name field)) (next remaining))))))
    spec))

(defn- semantic-block-spec [spec]
  (let [universes (:block/universes spec)
        universe-index (zipmap universes (range))
        parameters (:block/parameters spec)
        normalized-parameters
        (loop [known {}
               index 0
               remaining parameters
               result []]
          (if-let [{:parameter/keys [name type]} (fst remaining)]
            (recur (assoc known name [:parameter index])
                   (inc index) (next remaining)
                   (conj result
                         (normalize-block-type-ast type universe-index known)))
            {:types result :index known}))
        parameter-index (:index normalized-parameters)]
    {:rainbow/kind :inductive-block
     :block/schema-version 1
     :block/universe-count (count universes)
     :block/parameters
     (:types normalized-parameters)
     :block/sort-level (normalize-block-level (:block/sort-level spec) universe-index)
     :block/constructors
     (mapv (fn [constructor]
             (loop [known parameter-index
                    field-index 0
                    remaining (:constructor/fields constructor)
                    result []]
               (if-let [field (fst remaining)]
                 (let [field-type (:field/type field)
                       normalized
                       (if (= [:self] field-type)
                         [:self]
                         (normalize-block-type-ast field-type universe-index
                                                   known))]
                   (recur (assoc known (:field/name field) [:field field-index])
                          (inc field-index) (next remaining) (conj result normalized)))
                 result)))
           (:block/constructors spec))}))

(defn inductive-block-id [spec]
  (validate-block-spec! spec)
  (canonical/content-id (semantic-block-spec spec)))

(defn- member-id [block-id member-key]
  (canonical/content-id {:block/id block-id :block/member-key member-key}))

(defn- compile-block-ast [ast context]
  (case (fst ast)
    :var (if-some [index (fst (keep-indexed (fn [i name]
                                                (when (= name (snd ast)) i))
                                              context))]
           (term/bound index)
           (reject! :kernel/unknown-block-variable "Unknown block type variable"
                    {:variable (snd ast) :context context}))
    :sort (term/sort-term (snd ast))
    :const (term/constant (snd ast) (nth ast 2))
    :app (apply-arguments (compile-block-ast (snd ast) context)
                          (map #(compile-block-ast % context) (drop 2 ast)))
    :pi (let [[_ bindings body] ast]
          (letfn [(walk [remaining inner-context]
                    (if-let [[name type-ast] (fst remaining)]
                      (term/pi-term (compile-block-ast type-ast inner-context)
                                    (walk (next remaining) (into [name] inner-context)))
                      (compile-block-ast body inner-context)))]
            (walk bindings context)))))

(defn- compile-pi [bindings body]
  (letfn [(walk [remaining context]
            (if-let [[name type-ast] (fst remaining)]
              (term/pi-term (compile-block-ast type-ast context)
                            (walk (next remaining) (into [name] context)))
              (compile-block-ast body context)))]
    (walk bindings [])))

(defn- app-ast [function arguments]
  (if (seq arguments) (into [:app function] arguments) function))

(defn- block-members [spec block-id]
  (let [universes (:block/universes spec)
        universe-levels (mapv #(vector :param %) universes)
        parameters (:block/parameters spec)
        parameter-bindings (mapv (fn [{:parameter/keys [name type]}] [name type]) parameters)
        parameter-vars (mapv #(vector :var (:parameter/name %)) parameters)
        inductive-id (member-id block-id :inductive)
        inductive-head [:const inductive-id universe-levels]
        inductive-app (app-ast inductive-head parameter-vars)
        constructors (:block/constructors spec)
        constructor-ids (mapv #(member-id block-id [:constructor %])
                              (range (count constructors)))
        inductive-type (compile-pi parameter-bindings
                                   [:sort (:block/sort-level spec)])
        inductive-declaration
        {:rainbow/id inductive-id
         :rainbow/kind :inductive
         :rainbow/aliases #{(:block/alias spec)}
         :rainbow/universes universes
         :rainbow/type inductive-type
         :rainbow/value nil
         :rainbow/transparency :opaque
         :rainbow/dependencies (term/constants inductive-type)
         :rainbow/axioms #{}
         :rainbow/block-id block-id
         :rainbow/member-key :inductive
         :rainbow/schema-version 1}
        constructor-declarations
        (mapv
         (fn [index constructor constructor-id]
           (let [fields (:constructor/fields constructor)
                 field-bindings
                 (mapv (fn [{:field/keys [name type]}]
                         [name (if (= [:self] type) inductive-app type)])
                       fields)
                 constructor-type (compile-pi (into parameter-bindings field-bindings)
                                              inductive-app)]
             {:rainbow/id constructor-id
              :rainbow/kind :constructor
              :rainbow/aliases #{(:constructor/alias constructor)}
              :rainbow/universes universes
              :rainbow/type constructor-type
              :rainbow/value nil
              :rainbow/transparency :opaque
              :rainbow/dependencies (term/constants constructor-type)
              :rainbow/axioms #{}
              :rainbow/block-id block-id
              :rainbow/member-key [:constructor index]
              :rainbow/constructor {:index index
                                    :field-count (count fields)
                                    :recursive-fields (mapv #(= [:self] (:field/type %)) fields)}
              :rainbow/schema-version 1}))
         (range) constructors constructor-ids)
        motive-name '_motive
        target-name '_target
        motive-type [:pi [[target-name inductive-app]]
                     [:sort [:param motive-universe-parameter]]]
        case-bindings
        (mapv
         (fn [constructor-index constructor constructor-id]
           (let [fields (:constructor/fields constructor)
                 bindings
                 (reduce (fn [result [field-index field]]
                           (let [field-name (:field/name field)
                                 recursive? (= [:self] (:field/type field))
                                 field-type (if recursive? inductive-app (:field/type field))
                                 result (conj result [field-name field-type])]
                             (if recursive?
                               (conj result
                                     [(symbol (str "_ih_" constructor-index "_" field-index))
                                      (app-ast [:var motive-name] [[:var field-name]])])
                               result)))
                         [] (map-indexed vector fields))
                 constructor-term (app-ast [:const constructor-id universe-levels]
                                           (into parameter-vars
                                                 (mapv #(vector :var (:field/name %)) fields)))
                 case-type [:pi bindings
                            (app-ast [:var motive-name] [constructor-term])]]
             [(symbol (str "_case_" constructor-index)) case-type]))
         (range) constructors constructor-ids)
        recursor-id (member-id block-id :recursor)
        recursor-universes (conj universes motive-universe-parameter)
        recursor-type
        (compile-pi
         (into parameter-bindings
               (concat [[motive-name motive-type]]
                       case-bindings
                       [[target-name inductive-app]]))
         (app-ast [:var motive-name] [[:var target-name]]))
        recursor-declaration
        {:rainbow/id recursor-id
         :rainbow/kind :recursor
         :rainbow/aliases #{(symbol (str (:block/alias spec) ".rec"))}
         :rainbow/universes recursor-universes
         :rainbow/type recursor-type
         :rainbow/value nil
         :rainbow/transparency :opaque
         :rainbow/dependencies (term/constants recursor-type)
         :rainbow/axioms #{}
         :rainbow/block-id block-id
         :rainbow/member-key :recursor
         :rainbow/recursor {:block-id block-id
                            :parameter-count (count parameters)
                            :constructor-count (count constructors)}
         :rainbow/schema-version 1}]
    {:inductive inductive-declaration
     :constructors constructor-declarations
     :recursor recursor-declaration
     :members (into [inductive-declaration]
                    (conj constructor-declarations recursor-declaration))}))

;; Universe comparison for inductive fields (level-at-most*?, defined with the large-elimination rule
;; above): a SOUND, possibly incomplete test that level a <= level b under every assignment of universe
;; parameters. A level is read as the max of terms base + k; imax is bounded above by max on the left
;; and below by its right argument on the right.
(defn level-at-most?
  "True when a <= b holds for every assignment of universe parameters (sound, possibly incomplete)."
  [a b]
  (level-at-most*? a b))

(defn- assert-field-universes!
  "Every non-recursive constructor field lives in a universe at most the block's sort. Without this an
  inductive type can contain its own universe (U : Sort 1 with mk : Sort 1 -> U), and with the
  recursor's free motive universe that is Girard's paradox. There is no impredicative exception for
  Prop blocks: a Prop block with a large field and large elimination is Coquand's paradox."
  [environment spec constructor-declarations]
  (let [block-level (:block/sort-level spec)
        parameter-count (count (:block/parameters spec))]
    (doseq [[index constructor declaration] (map vector (range) (:block/constructors spec) constructor-declarations)]
      (loop [type (:rainbow/type declaration) context [] position 0
             fields (:constructor/fields constructor)]
        (when (= :pi (fst type))
          (let [domain (snd type)
                field (when (>= position parameter-count) (fst fields))]
            (when (and field (not= [:self] (:field/type field)))
              (let [field-level (sort-level! environment (infer* environment context domain))]
                (when-not (level-at-most? field-level block-level)
                  (reject! :kernel/field-universe-too-large
                           "Constructor field lives in a universe above the inductive type's sort"
                           {:constructor index :field (:field/name field)
                            :field-level field-level :sort-level block-level}))))
            (recur (nth type 2) (into [domain] context) (inc position)
                   (if field (next fields) fields))))))))

(defn add-inductive-block [environment spec]
  (try
    (validate-block-spec! spec)
    (let [block-id (inductive-block-id spec)
          supplied-id (:rainbow/id spec)
          _ (when (and supplied-id (not= supplied-id block-id))
              (reject! :kernel/forged-inductive-block-id
                       "Supplied block ID does not match its normalized descriptor"
                       {:supplied supplied-id :computed block-id}))
          {:keys [members] :as generated} (block-members spec block-id)
          aliases (mapcat :rainbow/aliases members)
          conflict (some (fn [alias]
                           (when-let [old (environment/resolve-id environment alias)]
                             [alias old]))
                         aliases)
          _ (when conflict
              (reject! :kernel/alias-conflict "Inductive alias already exists"
                       {:alias (fst conflict) :existing-id (snd conflict)}))
          block {:rainbow/id block-id
                 :rainbow/kind :inductive-block
                 :block/schema-version 1
                 :block/spec (dissoc spec :rainbow/id)
                 :block/semantic (semantic-block-spec spec)
                 :block/member-ids (mapv :rainbow/id members)}
          staged (-> environment
                     (assoc-in [:rainbow.environment/blocks block-id] block)
                     (update :rainbow.environment/block-order conj block-id)
                     (update :rainbow.environment/declarations
                             into (into {} (map (juxt :rainbow/id identity) members)))
                     (update :rainbow.environment/aliases
                             into (into {} (mapcat (fn [member]
                                                    (map (fn [alias]
                                                           [alias (:rainbow/id member)])
                                                         (:rainbow/aliases member)))
                                                  members)))
                     (update :rainbow.environment/order
                             into (mapv :rainbow/id members)))
          _ (doseq [member members]
              (when-not (= (:rainbow/id member) (environment/declaration-id member))
                (reject! :kernel/inductive-member-id
                         "Generated member ID is inconsistent" {:member member}))
              (term/assert-term! (:rainbow/type member))
              (when-not (term/closed? (:rainbow/type member))
                (reject! :kernel/free-variable "Generated inductive member type is open"
                         {:member (:rainbow/id member)}))
              (let [result (infer staged (:rainbow/type member)
                                  (set (:rainbow/universes member)))]
                (when-not (and (= :checked (:status result))
                               (= :sort (fst (:term (normalize staged (:type result))))))
                  (reject! :kernel/invalid-inductive-member-type
                           "Generated inductive member type failed kernel checking"
                           {:member (:rainbow/id member) :cause result}))))
          _ (assert-field-universes! staged spec (:constructors generated))
          staged (reduce (fn [env member]
                           (let [requirements (term-level-requirements env (:rainbow/type member))]
                             (cond-> env (seq requirements)
                               (assoc-in [:rainbow.environment/declarations (:rainbow/id member) :rainbow/level-requirements]
                                         requirements))))
                         staged members)
          ;; A member inherits the axioms of the constants in its type (a field or parameter
          ;; type may mention an axiom): every user's closure then sees them. Its own block's
          ;; members are not yet in `environment` and carry none.
          members (mapv #(assoc % :rainbow/axioms (declaration-axioms environment %)) members)
          staged (reduce (fn [env member]
                           (assoc-in env [:rainbow.environment/declarations (:rainbow/id member) :rainbow/axioms]
                                     (:rainbow/axioms member)))
                         staged members)]
      {:status :accepted
       :block block
       :declarations members
       :environment staged
       :generated generated})
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected
       :error (ex-data exception)
       :message (ex-message exception)})))

(defn axioms [environment id-or-alias]
  (when-let [id (environment/resolve-id environment id-or-alias)]
    (let [declaration (environment/declaration environment id)]
      (if (= :axiom (:rainbow/kind declaration))
        #{id}
        (:rainbow/axioms declaration)))))
