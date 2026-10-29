(ns rainbow.search-fast-path-test
  "The search's untrusted fast paths (proof/convertible?, the apply pre-test, context-trusting
  inference) must give the answers the kernel's own public entry points give."
  (:require [clojure.test :refer :all]
            [rainbow.history.nat-induction :as nat-induction]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

(def environment (delay (:environment (nat-induction/build))))

(defn- suffixes [type]
  (loop [current type result [type]]
    (let [body (when (= :pi (first current))
                 (try (term/shift (nth current 2) -1) (catch clojure.lang.ExceptionInfo _ nil)))]
      (if body (recur body (conj result body)) result))))

(defn- sample-types [env]
  (->> (vals (:rainbow.environment/declarations env))
       (filter #(and (empty? (:rainbow/universes %)) (#{:theorem :definition :axiom :inductive} (:rainbow/kind %))))
       (sort-by :rainbow/id)
       (mapcat (comp suffixes :rainbow/type))
       distinct (take 60) vec))

(deftest certain-distinctness-never-contradicts-the-kernel
  (let [env @environment types (sample-types env)
        decided (atom 0)]
    (doseq [a types b types]
      (let [kernel-equal? (true? (kernel/definitionally-equal? env a b))]
        (when (proof/distinct-normal-forms? env a b 24)
          (swap! decided inc)
          (is (not kernel-equal?) [a b]))
        (is (= kernel-equal? (proof/convertible? env a b)) [a b])))
    (is (pos? @decided))))

(deftest apply-pre-test-reaches-the-same-outcome-as-the-normalizing-plan
  (let [env @environment types (sample-types env)
        constants (->> (vals (:rainbow.environment/declarations env))
                       (filter #(and (empty? (:rainbow/universes %)) (#{:theorem :axiom} (:rainbow/kind %))))
                       (sort-by :rainbow/id) (take 25) (map #(term/constant (:rainbow/id %) [])))
        outcome #(let [r (tactic/run %1 (tactic/apply %2 {:independent-only? true}))]
                   [(:status r) (get-in r [:failure :failure/category]) (:goals r)])]
    (doseq [target types
            :let [started (proof/start env target)]
            :when (= :ready (:status started))
            constant constants]
      (is (= (with-redefs [rainbow.tactic/quick-application-failure (constantly nil)]
               (outcome (:state started) constant))
             (outcome (:state started) constant))
          [target constant]))))

(defn- reference-infer
  "The context-closing inference infer-in-context used before it trusted the goal's context."
  [env context expression]
  (let [result (kernel/infer env (proof/close-over-context context expression term/lambda-term) #{})]
    (when (= :checked (:status result))
      (loop [type (:type result) remaining (count context)]
        (if (zero? remaining) type (recur (nth type 2) (dec remaining)))))))

(deftest context-trusting-inference-agrees-with-closed-inference
  (let [env @environment
        goals (for [type (sample-types env)
                    :let [started (proof/start env type)]
                    :when (= :ready (:status started))
                    :let [state (:state (tactic/run (:state started) (tactic/repeat (tactic/intro) {:max 4})))]
                    :when state]
                (proof/current-goal state))]
    (doseq [goal (take 30 goals)
            :let [context (:goal/context goal)
                  seeds (map term/bound (range (count context)))]
            expression (concat seeds (for [f seeds a seeds] (term/application f a)))]
      (let [fast (proof/infer-in-context env context expression #{})]
        (is (= (reference-infer env context expression)
               (when (= :checked (:status fast)) (:type fast)))
            [context expression])))))
