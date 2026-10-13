(ns rainbow.kernel-test
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as string]
            [clojure.test :refer :all]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.term :as term]))

(defn accepted-environment [] (direct-term-corpus/build-environment))

(deftest eight-closed-proofs-are-kernel-accepted
  (let [checked (accepted-environment)]
    (is (= 8 (count (:rainbow.environment/declarations checked))))
    (is (= (set (map :name direct-term-corpus/proofs))
           (set (keys (:rainbow.environment/aliases checked)))))
    (doseq [{:keys [name]} direct-term-corpus/proofs]
      (is (= #{} (kernel/axioms checked name)) (str name " must be axiom-free")))))

(deftest beta-zeta-and-eta-definitional-equality
  (let [empty (environment/empty-environment)
        type (direct-term-corpus/s direct-term-corpus/u)
        identity (direct-term-corpus/lam type (direct-term-corpus/b 0))
        argument (direct-term-corpus/lam type (direct-term-corpus/b 0))
        beta (direct-term-corpus/app identity argument)
        zeta (term/let-term type argument (direct-term-corpus/b 0))
        eta (direct-term-corpus/lam type (direct-term-corpus/app (direct-term-corpus/b 1) (direct-term-corpus/b 0)))]
    (is (true? (kernel/definitionally-equal? empty beta argument)))
    (is (true? (kernel/definitionally-equal? empty zeta argument)))
    ;; Eta is open here, but definitional equality is a structural diagnostic API.
    (is (true? (kernel/definitionally-equal? empty eta (direct-term-corpus/b 0))))))

(deftest normalization-respects-resource-limits
  (let [expression (term/let-term (direct-term-corpus/s direct-term-corpus/u)
                                  (direct-term-corpus/s direct-term-corpus/u)
                                  (direct-term-corpus/b 0))]
    (is (= :resource-limit
           (:status (kernel/normalize (environment/empty-environment)
                                      expression
                                      {:reductions 0}))))))

(defn- balanced-beta-tree [depth]
  (if (zero? depth)
    (let [sort (direct-term-corpus/s direct-term-corpus/u)]
      (direct-term-corpus/app (direct-term-corpus/lam sort sort) sort))
    (let [branch (balanced-beta-tree (dec depth))]
      (direct-term-corpus/app branch branch))))

(deftest structural-reflexivity-does-not-spend-the-reduction-budget
  ;; The invariant under test -- structural reflexivity on identical immutable
  ;; proof data is free -- holds at any budget, so this uses a budget smaller
  ;; than the tree depth and keeps the suite fast.
  (let [expression (balanced-beta-tree 12)
        empty (environment/empty-environment)]
    ;; Normalizing this diagnostic term exceeds a small explicit budget...
    (is (= :resource-limit
           (:status (kernel/normalize empty expression {:reductions 5}))))
    ;; ...yet identical immutable proof data is reflexive without any conversion.
    (is (true? (kernel/definitionally-equal? empty expression expression)))
    ;; A structurally different term is distinguished at the head, not by
    ;; exhausting the budget.
    (is (false? (kernel/definitionally-equal? empty expression
                                              (direct-term-corpus/s direct-term-corpus/u))))))

(deftest normalization-memoizes-repeated-immutable-subterms
  (let [expression (balanced-beta-tree 12)
        result (kernel/normalize (environment/empty-environment)
                                 expression {:reductions 20})]
    ;; Without subterm sharing this balanced term needs 2^12 beta reductions.
    (is (= :normalized (:status result)))
    (is (<= (:reductions result) 20))))

(deftest full-conversion-reduces-functions-that-erase-arguments
  (let [sort (direct-term-corpus/s direct-term-corpus/u)
        constant-function (direct-term-corpus/lam sort sort)
        left (direct-term-corpus/app constant-function (direct-term-corpus/b 0))
        right (direct-term-corpus/app constant-function (direct-term-corpus/b 1))]
    ;; Beta reduction erases both unequal arguments and exposes equal results.
    (is (true? (kernel/definitionally-equal?
                (environment/empty-environment) left right)))))

(deftest successor-max-universes-normalize-canonically
  (let [u [:param 'u]]
    (is (= [:succ u]
           (term/normalize-level
            [:max [:succ [:zero]] [:succ u]])))
    (is (= [:succ [:max u [:param 'v]]]
           (term/normalize-level
            [:max [:succ u] [:succ [:param 'v]]])))))

(defn base-identity []
  (direct-term-corpus/declaration (first direct-term-corpus/proofs)))

(def corruptions
  [{:name :malformed-type-op
    :change #(assoc % :rainbow/type [:bogus])}
   {:name :negative-bound
    :change #(assoc % :rainbow/type [:bound -1])}
   {:name :free-variable-type
    :change #(assoc % :rainbow/type [:bound 0])}
   {:name :missing-value
    :change #(assoc % :rainbow/value nil)}
   {:name :axiom-with-value
    :change #(assoc % :rainbow/kind :axiom)}
   {:name :unsupported-kind
    :change #(assoc % :rainbow/kind :inductive)}
   {:name :wrong-outer-domain
    :change #(assoc-in % [:rainbow/value 1] (direct-term-corpus/s [:succ direct-term-corpus/u]))}
   {:name :unbound-value
    :change #(assoc % :rainbow/value (direct-term-corpus/b 0))}
   {:name :non-function-application
    :change #(assoc % :rainbow/value
                    (direct-term-corpus/lam (direct-term-corpus/s direct-term-corpus/u)
                              (direct-term-corpus/lam (direct-term-corpus/b 0)
                                        (direct-term-corpus/app (direct-term-corpus/b 0) (direct-term-corpus/b 0)))))}
   {:name :implicit-lambda
    :change #(assoc-in % [:rainbow/value 3] :implicit)}
   {:name :undeclared-universe
    :change #(assoc % :rainbow/universes [])}
   {:name :duplicate-universes
    :change #(assoc % :rainbow/universes ['u 'u])}
   {:name :false-dependency
    :change #(assoc % :rainbow/dependencies #{"sha256:missing"})}
   {:name :bad-transparency
    :change #(assoc % :rainbow/transparency :transparent)}
   {:name :forged-id
    :change #(assoc % :rainbow/id "sha256:forged")}
   {:name :bad-schema
    :change #(assoc % :rainbow/schema-version 2)}
   {:name :bad-alias-container
    :change #(assoc % :rainbow/aliases ['logic/not-a-set])}
   {:name :bad-alias-value
    :change #(assoc % :rainbow/aliases #{:not-a-symbol})}
   {:name :malformed-let
    :change #(assoc % :rainbow/value [:let (direct-term-corpus/s direct-term-corpus/u) (direct-term-corpus/s direct-term-corpus/u)])}
   {:name :term-as-type
    :change #(assoc % :rainbow/type
                    (direct-term-corpus/lam (direct-term-corpus/s direct-term-corpus/u) (direct-term-corpus/b 0)))}
   {:name :wrong-result
    :change #(assoc % :rainbow/value
                    (direct-term-corpus/lam (direct-term-corpus/s direct-term-corpus/u)
                              (direct-term-corpus/lam (direct-term-corpus/b 0) (direct-term-corpus/b 1))))}])

(deftest at-least-twenty-structural-corruptions-are-rejected
  (is (<= 20 (count corruptions)))
  (doseq [{:keys [name change]} corruptions]
    (let [result (kernel/add-declaration (environment/empty-environment)
                                         (change (base-identity)))]
      (is (= :rejected (:status result)) (str name " was unexpectedly accepted"))
      (is (keyword? (get-in result [:error :error/category]))
          (str name " did not return a structured error")))))

(deftest wrong-constant-universe-arity-is-rejected
  (let [checked (accepted-environment)
        id (environment/resolve-id checked 'logic/polymorphic-identity)
        identity (first direct-term-corpus/proofs)
        candidate {:rainbow/kind :theorem
                   :rainbow/aliases #{'logic/bad-reference}
                   :rainbow/universes ['u]
                   :rainbow/type (:type identity)
                   :rainbow/value (term/constant id [])
                   :rainbow/transparency :opaque
                   :rainbow/dependencies #{id}
                   :rainbow/schema-version 1}
        result (kernel/add-declaration checked candidate)]
    (is (= :rejected (:status result)))
    (is (= :kernel/invalid-declaration-value
           (get-in result [:error :error/category])))))

(deftest aliases-do-not-change-semantic-identity
  (let [candidate (base-identity)
        first-result (kernel/add-declaration (environment/empty-environment) candidate)
        with-alias (update candidate :rainbow/aliases conj 'logic/id)
        second-result (kernel/add-declaration (environment/empty-environment) with-alias)]
    (is (= (get-in first-result [:declaration :rainbow/id])
           (get-in second-result [:declaration :rainbow/id])))
    (is (= (environment/environment-id (:environment first-result))
           (environment/environment-id (:environment second-result))))))

(defn java-command [& arguments]
  (apply shell/sh
         (str (System/getProperty "java.home") "/bin/java")
         "-cp" (System/getProperty "java.class.path")
         "clojure.main"
         arguments))

(deftest checked-declarations-persist-and-replay-in-a-fresh-jvm
  (let [path (.getAbsolutePath (java.io.File/createTempFile "rainbow-day1-" ".edn"))
        checked (accepted-environment)
        save-result (persistence/save-environment! checked path)
        local-result (persistence/load-environment path)
        process-result (java-command "-m" "rainbow.history.direct-term-corpus" "replay" path)]
    (try
      (is (= :saved (:status save-result)))
      (is (= :replayed (:status local-result)))
      (is (= (environment/environment-id checked) (:environment-id local-result)))
      (is (zero? (:exit process-result)) (:err process-result))
      (is (.contains ^String (:out process-result) ":status :replayed"))
      (finally
        (.delete (io/file path))))))

(deftest semantic-hashes-and-normal-forms-match-across-twenty-fresh-jvms
  (let [runs (repeatedly 20 #(java-command "-m" "rainbow.history.direct-term-corpus" "hash"))]
    (doseq [run runs]
      (is (zero? (:exit run)) (:err run))
      (is (empty? (:err run))))
    (is (= 1 (count (set (map :out runs)))))
    (let [[environment-id normal-forms-id] (string/split
                                             (string/trim (:out (first runs)))
                                             #"\t")]
      (is (.startsWith environment-id "sha256:"))
      (is (.startsWith normal-forms-id "sha256:")))))
