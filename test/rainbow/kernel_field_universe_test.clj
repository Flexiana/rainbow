(ns rainbow.kernel-field-universe-test
  "An inductive type's constructor fields must live in universes at most its own sort. Without the check
  the kernel accepted U : Sort 1 with mk : Sort 1 -> U, and the recursor's free motive universe then gives
  proj : U -> Sort 1 with proj (mk A) = A: a type that contains its own universe (Girard's paradox)."
  (:require [clojure.test :refer [deftest is]]
            [clojure.walk :as walk]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.kernel :as kernel]))

(def base
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "Checkpoint rejected" {})))
           (:environment cp))))

(def one [:succ [:zero]])
(defn- block [alias level universes parameters fields]
  {:block/schema-version 1 :block/alias alias :block/universes universes :block/parameters parameters
   :block/sort-level level
   :block/constructors [{:constructor/alias (symbol "probe" (str (name alias) "-mk")) :constructor/fields fields}]})
(defn- add [spec] (kernel/add-inductive-block @base spec))
(defn- rejected-for-universe? [r]
  (and (= :rejected (:status r)) (= :kernel/field-universe-too-large (get-in r [:error :error/category]))))

(deftest a-type-cannot-contain-its-own-universe
  ;; the reported counterexample
  (is (rejected-for-universe? (add (block 'probe/U one [] [] [{:field/name 'A :field/type [:sort one]}]))))
  ;; the same one level up, and universe-polymorphically
  (is (rejected-for-universe? (add (block 'probe/U2 [:succ one] [] [] [{:field/name 'A :field/type [:sort [:succ one]]}]))))
  (is (rejected-for-universe? (add (block 'probe/Uu [:param 'u] '[u] [] [{:field/name 'A :field/type [:sort [:param 'u]]}]))))
  ;; a Prop block may not hold a type (no impredicative exception: Coquand's paradox)
  (is (rejected-for-universe? (add (block 'probe/BigProp [:zero] [] [] [{:field/name 'A :field/type [:sort [:zero]]}]))))
  ;; a field behind a function type counts at its imax level
  (is (rejected-for-universe? (add (block 'probe/Fun one [] [] [{:field/name 'F :field/type [:pi [['x [:sort one]]] [:sort [:zero]]]}])))))

(deftest small-fields-are-still-accepted
  (is (= :accepted (:status (add (block 'probe/Big [:succ one] [] [] [{:field/name 'A :field/type [:sort one]}])))))
  (is (= :accepted (:status (add (block 'probe/Box [:param 'u] '[u] [{:parameter/name 'A :parameter/type [:sort [:param 'u]]}]
                                        [{:field/name 'a :field/type [:var 'A]}])))))
  (is (= :accepted (:status (add (block 'probe/Up [:succ [:param 'u]] '[u] [] [{:field/name 'A :field/type [:sort [:param 'u]]}])))))
  ;; a Prop block over a proposition parameter, and a Prop-valued function field
  (is (= :accepted (:status (add (block 'probe/PBox [:zero] [] [{:parameter/name 'P :parameter/type [:sort [:zero]]}]
                                        [{:field/name 'p :field/type [:var 'P]}])))))
  (is (= :accepted (:status (add (block 'probe/PFun [:zero] [] [{:parameter/name 'P :parameter/type [:sort [:zero]]}]
                                        [{:field/name 'f :field/type [:pi [['x [:sort one]]] [:var 'P]]}]))))))

(deftest every-existing-block-passes-the-check
  ;; re-add each block of the checkpoint under fresh aliases: none may be rejected by the new check
  (let [env @base blocks (vals (:rainbow.environment/blocks env))]
    (is (pos? (count blocks)))
    (doseq [b blocks]
      (let [spec (:block/spec b)
            aliases (into [(:block/alias spec)] (map :constructor/alias (:block/constructors spec)))
            fresh (zipmap aliases (map #(symbol "probe-copy" (str (namespace %) "." (name %))) aliases))
            spec' (-> spec (dissoc :rainbow/id)
                      (assoc :block/alias (fresh (:block/alias spec)))
                      (update :block/constructors (fn [cs] (mapv #(update % :constructor/alias fresh) cs))))
            r (kernel/add-inductive-block env spec')]
        (is (= :accepted (:status r)) (str (:block/alias spec) " " (:message r) " " (pr-str (:error r))))))))

(deftest level-comparison-is-sound-on-cases
  (let [u [:param 'u] v [:param 'v] z [:zero]]
    (is (kernel/level-at-most? z u))
    (is (kernel/level-at-most? u [:succ u]))
    (is (not (kernel/level-at-most? [:succ u] u)))
    (is (not (kernel/level-at-most? u v)))
    (is (kernel/level-at-most? u [:max u v]))
    (is (kernel/level-at-most? [:max u v] [:succ [:max u v]]))
    (is (not (kernel/level-at-most? [:max u v] u)))
    (is (kernel/level-at-most? [:imax u v] [:max u v]))
    (is (kernel/level-at-most? v [:imax u v]))
    (is (not (kernel/level-at-most? u [:imax u v])))
    (is (not (kernel/level-at-most? one z)))
    (is (kernel/level-at-most? one [:succ u]))))
