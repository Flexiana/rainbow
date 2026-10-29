(ns rainbow.simp-test
  "rainbow.simp: rule orientation, conditional rewriting, loop detection, kernel-checked proof
  terms, the reuse hold-out, and the search step (:native-simp?)."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.equality :as equality]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]
            [rainbow.simp :as simp]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

(defn- c [alias] [:const alias []])
(defn- ap [f & xs] (into [:app f] xs))
(defn- eqT [x y] (ap [:const 'equality/Eq [[:succ [:zero]]]] (c 't/T) x y))
(def ^:private T (c 't/T))

;; A postulated type T with f g h : T -> T (h binary), a b : T and P : T -> Prop. Each rule is an
;; axiom (`-ax`) restated as a theorem, so the reuse index (theorems only) holds it.
(def ^:private specs
  [['t/T :axiom [:sort [:succ [:zero]]]]
   ['t/f :axiom [:-> T T]] ['t/g :axiom [:-> T T]] ['t/h :axiom [:-> T T T]]
   ['t/a :axiom T] ['t/b :axiom T] ['t/P :axiom [:-> T 'Prop]]
   ;; stated small-to-large: orientation turns it into f (g x) -> x
   ['t/fg-ax :axiom [:forall [['x T]] (eqT 'x (ap (c 't/f) (ap (c 't/g) 'x)))]]
   ;; conditional: P x -> g x = x
   ['t/cond-ax :axiom [:forall [['x T] ['p (ap (c 't/P) 'x)]] (eqT (ap (c 't/g) 'x) 'x)]]
   ;; permutative: h x y = h y x
   ['t/comm-ax :axiom [:forall [['x T] ['y T]] (eqT (ap (c 't/h) 'x 'y) (ap (c 't/h) 'y 'x))]]])

(defn- add [env [name kind type value]]
  (let [elab #(if (term/term? %) % (:term (elaborate/core-expression env %)))
        type (elab type) value (when value (elab value))
        result (kernel/add-declaration
                env {:rainbow/kind kind :rainbow/aliases #{name} :rainbow/universes [] :rainbow/type type
                     :rainbow/value value :rainbow/transparency :opaque
                     :rainbow/dependencies (into (term/constants type) (when value (term/constants value)))
                     :rainbow/provenance {:origin :native :producer :test} :rainbow/schema-version 1})]
    (assert (= :accepted (:status result)) (pr-str result))
    (:environment result)))

(def ^:private env
  (delay
    (let [env (reduce add (equality/build-environment) specs)
          theorem (fn [env name axiom]
                    (let [axiom-id (environment/resolve-id env axiom)]
                      (add env [name :theorem (:rainbow/type (environment/declaration env axiom-id))
                                [:const axiom-id []]])))]
      (-> env (theorem 't/fg 't/fg-ax) (theorem 't/cond 't/cond-ax) (theorem 't/comm 't/comm-ax)))))

(defn- id [alias] (environment/resolve-id @env alias))
(def ^:private axioms (delay (set (map id '[t/T t/f t/g t/h t/a t/b t/P t/fg-ax t/cond-ax t/comm-ax]))))
(defn- index ([] (index nil)) ([include] (reuse/build-index @env (cond-> {} include (assoc :include-ids (map id include))))))
(defn- options [idx] {:reuse-index idx :reuse-policy {:allowed-axioms @axioms}})
(defn- core [surface] (:term (elaborate/core-expression @env surface)))
(defn- start [surface] (:state (proof/start @env (core surface))))

(defn- simp-proof
  "The closing simp step's proof of `surface`, after kernel/check against it, or nil."
  [surface idx]
  (let [step (first (simp/steps (start surface) (options idx)))]
    (when (= :exact (:tactic step))
      (is (= :checked (:status (kernel/check @env (:term step) (core surface) #{})))
          "every simp proof is kernel-checked against its goal")
      (:term step))))

(deftest rules-are-oriented-towards-the-smaller-side
  (let [rule (#'simp/declaration-rule @env (id 't/fg))
        [oriented] (#'simp/orient rule)]
    (is (= :backward (:direction oriented)) "x = f (g x) rewrites f (g x) to x")
    (is (= [(id 't/f) 1] (#'simp/key-of (:lhs oriented))))
    (testing "the stated small-to-large equation closes a goal that needs it right to left"
      (is (some? (simp-proof (eqT (ap (c 't/f) (ap (c 't/g) (c 't/a))) (c 't/a)) (index)))))
    (testing "a permutative rule keeps both directions out of a loop: one rewrite, then reflexivity"
      (is (some? (simp-proof (eqT (ap (c 't/h) (c 't/a) (c 't/b)) (ap (c 't/h) (c 't/b) (c 't/a))) (index)))))))

(deftest conditional-rules-discharge-their-premises
  (let [goal (fn [premise?] (cond->> (eqT (ap (c 't/f) (ap (c 't/g) (c 't/a))) (ap (c 't/f) (c 't/a)))
                              premise? (vector :-> (ap (c 't/P) (c 't/a)))))
        proof (simp-proof (goal true) (index '[t/cond]))]
    (is (some? proof) "g a = a under the hypothesis P a, then reflexivity")
    (is (contains? (term/constants proof) (id 't/cond)))
    (is (nil? (simp-proof (goal false) (index '[t/cond]))) "without P a the rule does not fire")))

(deftest rewriting-stops-at-a-visited-term
  (let [;; hypotheses a = b and b = a: rewriting a -> b -> a would cycle; the memo stops it
        surface [:-> (eqT (c 't/a) (c 't/b)) (eqT (c 't/b) (c 't/a)) (ap (c 't/P) (ap (c 't/f) (c 't/a))) (ap (c 't/P) (ap (c 't/f) (c 't/b)))]
        unprovable [:-> (eqT (c 't/a) (c 't/b)) (eqT (c 't/b) (c 't/a)) (ap (c 't/P) (c 't/a))]
        state (start unprovable)
        intro (:state (tactic/run state (tactic/repeat (tactic/intro) {:max 3})))
        started (System/nanoTime)
        steps (simp/steps intro (assoc (options (index)) :simp-fuel 1000000))]
    (is (some? (simp-proof surface (index))) "P (f a) follows from P (f b) by rewriting with a = b")
    (is (not-any? #(= :exact (:tactic %)) steps) "P a has no proof here")
    (is (< (/ (- (System/nanoTime) started) 1e6) 5000.0) "terminates well inside a large budget")))

(deftest held-out-rules-are-never-used
  (let [goal (eqT (ap (c 't/f) (ap (c 't/g) (c 't/a))) (c 't/a))]
    (is (some? (simp-proof goal (index '[t/fg]))))
    (is (nil? (simp-proof goal (index '[t/comm]))) "t/fg is outside the index: no proof")
    (is (nil? (simp-proof goal nil)) "no index: local hypotheses and definitions only")))

(deftest search-uses-simp-only-when-asked
  (let [goal (eqT (ap (c 't/f) (ap (c 't/g) (c 't/a))) (c 't/a))
        run #(search/prove (start goal) (merge {:states 50 :wall-ms 20000} (options (index '[t/fg])) %))
        with (run {:native-simp? true})]
    (is (= :proved (:status with)))
    (is (= :checked (:status (kernel/check @env (get-in with [:proof :proof/term]) (core goal) #{}))))
    (is (not= :proved (:status (run {}))) "the rule is backwards for rewrite and reuse")))
