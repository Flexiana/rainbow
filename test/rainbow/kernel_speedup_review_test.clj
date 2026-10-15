(ns rainbow.kernel-speedup-review-test
  "Adversarial comparisons against the complete, frozen pre-optimization kernel."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.data.inductive :as inductive]
            [rainbow.environment :as env]
            [rainbow.kernel :as k]
            [rainbow.kernel-test :as core-test]
            [rainbow.kernel-native-test :as native]
            [rainbow.kernel-speedup-reference.kernel :as old]
            [rainbow.kernel-speedup-reference.term :as old-term]
            [rainbow.term :as term]))

(def empty-env (env/empty-environment))
(def prop [:sort [:zero]])
(def type0 [:sort [:succ [:zero]]])
(defn app [f & xs] (reduce #(vector :app %1 %2) f xs))
(defn lam [body] [:lam prop body :explicit])
(defn verdict [r] (if (map? r) (:status r) r))
(defn outcome [f]
  (try (f) (catch Exception e {:thrown (str (class e)) :data (ex-data e)})))

(deftest eta-does-not-erase-non-eta-binder-modes
  (doseq [domain [prop type0]
          body [[:bound 0] prop (lam [:bound 1])]]
    (let [l [:lam domain body :explicit]
          r [:lam domain body :implicit]]
      (is (= (old/definitionally-equal? empty-env l r)
             (k/definitionally-equal? empty-env l r)) (pr-str l r)))))

(deftest eta-shortcuts-do-not-contract-before-a-beta-redex
  (doseq [inner [[:lam type0 prop :explicit] [:lam prop prop :implicit]]]
    (let [outer [:lam prop (app inner [:bound 0]) :explicit]]
      (is (false? (old/definitionally-equal? empty-env outer inner)))
      (is (= (old/definitionally-equal? empty-env outer inner)
             (k/definitionally-equal? empty-env outer inner))))))

(deftest same-head-congruence-does-not-ignore-invalid-constants
  (let [unknown [:const "sha256:missing" []]
        p [:app (lam [:bound 0]) prop]
        l (app unknown p)
        r (app unknown prop)]
    (is (false? (old/definitionally-equal? empty-env l r)))
    (is (= (old/definitionally-equal? empty-env l r)
           (k/definitionally-equal? empty-env l r)))))

(deftest unknown-constants-in-erased-arguments-remain-erasable
  (let [t (app (lam prop) [:const "sha256:missing" []])]
    (is (true? (old/definitionally-equal? empty-env t prop)))
    (is (true? (k/definitionally-equal? empty-env t prop)))))

(deftest congruence-does-not-skip-malformed-recursor-targets
  (let [e @@#'native/env
        c #(vector :const (env/resolve-id e %) [])
        bad (app [:const (env/resolve-id e 'data/Nat.rec) [[:succ [:zero]]]]
                 prop (c 'data/zero) (lam [:bound 0]) (c 'data/succ))
        common (app [:bound 0] bad)
        l (app common (app (lam [:bound 0]) prop))
        r (app common prop)]
    (is (= :rejected (:status (old/normalize e bad))))
    (is (false? (old/definitionally-equal? e l r)))
    (is (= (old/definitionally-equal? e l r) (k/definitionally-equal? e l r)))))

(deftest equality-does-not-reuse-another-environments-reference-validity
  (let [added (old/add-declaration empty-env
                                 {:rainbow/kind :axiom :rainbow/aliases #{'review/opaque}
                                  :rainbow/type [:pi prop prop :explicit]})
        e (:environment added)
        c [:const (env/resolve-id e 'review/opaque) []]
        l (app c (app (lam [:bound 0]) prop))
        r (app c prop)]
    (is (= :accepted (:status added)))
    (doseq [current [e empty-env e empty-env]]
      (is (= (old/definitionally-equal? current l r)
             (k/definitionally-equal? current l r))))))

(deftest native-steps-respect-transparency-and-pinned-identity
  (let [e @@#'native/env
        z [:const (env/resolve-id e 'data/zero) []]]
    (doseq [[id [arity _]] @#'k/nat-operations]
      (let [original (env/declaration e id)
            candidate (-> original (dissoc :rainbow/id)
                          (assoc :rainbow/transparency :opaque :rainbow/aliases #{}))
            a (old/add-declaration e candidate)
            b (k/add-declaration e candidate)
            opaque-id (get-in b [:declaration :rainbow/id])
            expression (apply app [:const opaque-id []] (repeat arity z))]
        (is (= :accepted (:status a) (:status b)))
        (is (not= id opaque-id))
        (is (= (select-keys (old/normalize (:environment a) expression) [:status :term])
               (select-keys (k/normalize (:environment b) expression) [:status :term])))
        (is (= expression (:term (k/normalize (:environment b) expression))))))))

(deftest native-operations-preserve-universe-arity-rejection
  (let [e @#'native/env
        e @e
        zero [:const (env/resolve-id e 'data/zero) []]]
    (doseq [[id [arity _]] @#'k/nat-operations
            levels [[[:zero]] [[:succ [:zero]] [:zero]]]]
      (let [expression (apply app [:const id levels] (repeat arity zero))
            reference (old/normalize e expression)
            actual (k/normalize e expression)]
        (is (= :rejected (:status reference)))
        (is (= (select-keys reference [:status :term])
               (select-keys actual [:status :term])) (str id " " levels))))))

(deftest all-six-native-operations-agree-with-the-frozen-kernel
  (let [e @@#'native/env
        z [:const (env/resolve-id e 'data/zero) []]
        s [:const (env/resolve-id e 'data/succ) []]
        numeral #(nth (iterate (fn [x] (app s x)) z) %)]
    (doseq [[id [arity _]] @#'k/nat-operations
            a (range 7) b (if (= arity 1) [0] (range 7))]
      (let [expression (apply app [:const id []] (map numeral (take arity [a b])))
            reference (old/normalize e expression)
            actual (k/normalize e expression)]
        (is (= :normalized (:status reference)))
        (is (= (select-keys reference [:status :term])
               (select-keys actual [:status :term])) (str id " " a " " b))))))

(deftest initial-inductives-and-checked-declarations-have-identical-verdicts
  (doseq [spec inductive/initial-specs]
    (let [a (old/add-inductive-block empty-env spec)
          b (k/add-inductive-block empty-env spec)]
      (is (= :accepted (:status a) (:status b)))
      (is (= (:block a) (:block b)))
      (is (= (:declarations a) (:declarations b)))))
  (doseq [proof direct-term-corpus/proofs
          :let [declaration (direct-term-corpus/declaration proof)]
          candidate [declaration
                     (assoc declaration :rainbow/value prop)
                     (assoc declaration :rainbow/value [:bound 0])
                     (assoc declaration :rainbow/universes [])]]
    (is (= (:status (old/add-declaration empty-env candidate))
           (:status (k/add-declaration empty-env candidate))) (str (:name proof)))))

(deftest declaration-rejection-matrix-agrees-with-the-frozen-kernel
  (doseq [{:keys [name change]} core-test/corruptions
          :let [d (change (core-test/base-identity))]]
    (is (= :rejected (:status (old/add-declaration empty-env d))
           (:status (k/add-declaration empty-env d))) (str name))))

(deftest well-typed-proof-checking-with-beta-wrappers-is-unchanged
  (doseq [{:keys [type value universes]} direct-term-corpus/proofs
          :let [parameters (set universes)
                beta (app [:lam type [:bound 0] :explicit] value)
                zeta [:let type value [:bound 0]]]
          expression [value beta zeta]
          expected [type prop type0]]
    (let [before (:status (old/check empty-env expression expected parameters))
          after (:status (k/check empty-env expression expected parameters))]
      (when (= expected type) (is (= :checked before after)))
      (is (= before after) (pr-str expression expected)))))

(deftest exhausted-reduction-remains-a-non-verdict
  (let [beta (app (lam [:bound 0]) prop)]
    (binding [k/*reduction-budget* 0 old/*reduction-budget* 0]
      (is (= :resource-limit (verdict (old/definitionally-equal? empty-env beta prop))))
      (is (= :resource-limit (verdict (k/definitionally-equal? empty-env beta prop))))
      (is (true? (old/definitionally-equal? empty-env beta beta)))
      (is (true? (k/definitionally-equal? empty-env beta beta))))))

(deftest native-fuel-cost-is-an-explicit-compatibility-exception
  ;; The accepted mathematical equation is unchanged, but one native step costs
  ;; less than delta/beta/iota. Exact finite-budget verdict identity is not true.
  (let [e @@#'native/env
        z [:const (env/resolve-id e 'data/zero) []]
        one (app [:const (env/resolve-id e 'data/succ) []] z)
        sum (app [:const (env/resolve-id e 'algebra/nat-add) []] z z)]
    (binding [k/*reduction-budget* 1 old/*reduction-budget* 1]
      (is (= :resource-limit (verdict (old/definitionally-equal? e sum z))))
      (is (true? (k/definitionally-equal? e sum z)))
      (is (false? (k/definitionally-equal? e sum one))))
    (binding [k/*reduction-budget* 0]
      (is (= :resource-limit (verdict (k/definitionally-equal? e sum z)))))))

(deftest beta-zeta-eta-and-universes-agree-on-normal-forms
  (let [levels [[:zero] [:succ [:zero]] [:param 'u]
                [:max [:zero] [:param 'u]] [:imax [:succ [:zero]] [:zero]]]
        terms (vec (concat
                    (map #(vector :sort %) levels)
                    [[:bound 0] (lam [:bound 0]) (lam prop)
                     (lam (app [:bound 1] [:bound 0]))]))
        terms (into terms (for [t terms]
                            [:let prop t [:app (lam [:bound 0]) [:bound 0]]]))]
    (doseq [t terms]
      (is (= (select-keys (old/normalize empty-env t) [:status :term])
             (select-keys (k/normalize empty-env t) [:status :term])) (pr-str t)))
    (doseq [l terms r terms]
      (is (= (verdict (old/definitionally-equal? empty-env l r))
             (verdict (k/definitionally-equal? empty-env l r))) (pr-str l r)))))

(deftest universe-caches-are-independent-of-substitution-order-and-thread
  (let [body [:pi [:sort [:max [:zero] [:param 'u]]]
              [:app [:const "sha256:poly" [[:param 'u] [:param 'v]]]
               [:bound 0]] :explicit]
        equal-copy (read-string (pr-str body))
        substitutions [{} {'u [:zero]} {'u [:succ [:zero]] 'v [:zero]} {}]
        check-all (fn []
                    (every? true?
                            (for [b [body equal-copy] s substitutions]
                              (= (old-term/instantiate-universes b s)
                                 (term/instantiate-universes b s)))))]
    (is (not (identical? body equal-copy)))
    (is (check-all))
    (let [workers (vec (repeatedly 4 #(future (check-all))))]
      (is (every? true? (map deref workers))))
    (is (check-all))))

(deftest dropping-identity-cache-entries-does-not-change-results
  (doseq [^ThreadLocal local [@#'term/ranges @#'term/level-normalized]]
    (let [previous (.get local)
          clears (atom 0)
          cache (proxy [java.util.IdentityHashMap] []
                  (size [] 1000001)
                  (clear [] (swap! clears inc) (proxy-super clear)))
          body [:pi [:sort [:max [:zero] [:param 'u]]]
                [:app [:bound 2] [:bound 0]] :explicit]]
      (try
        (.set local cache)
        (is (= (old-term/instantiate body [:bound 1]) (term/instantiate body [:bound 1])))
        (is (= (old-term/instantiate-universes body {}) (term/instantiate-universes body {})))
        (is (pos? @clears))
        (finally (.set local previous))))))

(deftest range-optimization-does-not-overflow-valid-large-indices
  (doseq [i [Long/MAX_VALUE (inc' Long/MAX_VALUE)]
          :let [b [:bound i]]]
    (is (= (outcome #(old-term/shift b 0))
           (outcome #(term/shift b 0))))
    (is (= (outcome #(old-term/instantiate [:bound 0] b))
           (outcome #(term/instantiate [:bound 0] b))))
    (is (= (outcome #(old/normalize empty-env [:lam prop (app b [:bound 0]) :explicit]))
           (outcome #(k/normalize empty-env [:lam prop (app b [:bound 0]) :explicit]))))))

(deftest huge-literal-expansion-returns-a-resource-result
  ;; These counts cannot be narrowed to a nonnegative int by nth. The public
  ;; boundary must report a limit instead of overflowing or wrapping to zero.
  (doseq [n [Long/MAX_VALUE 4294967296N]]
    (let [result (outcome #(k/normalize @@#'native/env [:nat n] {:reductions 2}))]
      (is (= :resource-limit (:status result)) (pr-str result)))))

(deftest unary-output-budget-is-shared-and-independent-of-proof-checking
  (let [e @@#'native/env
        nat [:const (env/resolve-id e 'data/Nat) []]
        large [:nat 4294967296N]
        pair [:app [:nat 2] [:nat 2]]]
    (is (= :checked (:status (k/check e large nat))))
    (is (= large (:term (k/normalize e large {::k/literals true :reductions 0}))))
    (is (= :resource-limit (:status (k/normalize e pair {:max-unary-nodes 3}))))
    (is (= :normalized (:status (k/normalize e pair {:max-unary-nodes 4 :reductions 0}))))
    (is (= :normalized (:status (k/normalize e [:nat 0] {:max-unary-nodes 0}))))
    (is (= :resource-limit (:status (k/normalize e [:nat 1] {:max-unary-nodes 0}))))))

(defn- terminating-term [^java.util.Random random depth]
  (if (zero? depth)
    (nth [prop type0 [:bound 0] [:bound 1]
          [:const "sha256:unknown" []]] (.nextInt random 5))
    (let [t (terminating-term random (dec depth))]
      (case (.nextInt random 7)
        0 (app (lam [:bound 0]) t)
        1 [:let prop t [:bound 0]]
        2 (app [:bound 0] t)
        3 [:lam prop t :explicit]
        4 [:lam type0 t :implicit]
        5 [:pi prop t :explicit]
        (app (lam prop) t)))))

(deftest seeded-terminating-diagnostic-comparisons-match-the-frozen-kernel
  (let [random (java.util.Random. 2026101501)]
    (dotimes [_ 600]
      (let [l (terminating-term random 5)
            other (terminating-term random 5)]
        (doseq [r [other (app (lam [:bound 0]) l) [:let prop l [:bound 0]]]]
          (is (= (verdict (old/definitionally-equal? empty-env l r))
                 (verdict (k/definitionally-equal? empty-env l r))) (pr-str l r)))))))
