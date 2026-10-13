(ns rainbow.data.list-test
  (:require [clojure.java.shell :as shell]
            [clojure.test :refer :all]
            [rainbow.data.inductive :as inductive]
            [rainbow.data.list :as list-data]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def checked-corpus (delay (list-data/build)))

(defn java-command [& arguments]
  (apply shell/sh
         (str (System/getProperty "java.home") "/bin/java")
         "-cp" (System/getProperty "java.class.path")
         "clojure.main"
         arguments))

(defn core-terms [environment]
  (let [level list-data/type-level
        nat (inductive/constant environment 'data/Nat [])
        zero (inductive/constant environment 'data/zero [])
        successor (inductive/constant environment 'data/succ [])
        nil-term (inductive/apply* (inductive/constant environment 'data/nil [level]) nat)
        cons-term (inductive/constant environment 'data/cons [level])
        one (inductive/apply* successor zero)
        two (inductive/apply* successor one)
        singleton-zero (inductive/apply* cons-term nat zero nil-term)
        singleton-one (inductive/apply* cons-term nat one nil-term)
        zero-one (inductive/apply* cons-term nat zero singleton-one)]
    {:level level :nat nat :zero zero :successor successor :one one :two two
     :nil-term nil-term :cons cons-term :singleton-zero singleton-zero
     :singleton-one singleton-one :zero-one zero-one}))

(deftest parameterized-list-block-and-definitions-kernel-check
  (let [{:keys [environment]} @checked-corpus]
    (is (= 5 (count (:rainbow.environment/blocks environment))))
    (is (= 84 (count (:rainbow.environment/declarations environment))))
    (doseq [alias '[data/List data/nil data/cons data/List.rec
                    list/length list/append list/map]]
      (is (environment/resolve-id environment alias) (str alias " must resolve"))
      (is (= #{} (kernel/axioms environment alias)) (str alias " must be axiom-free")))
    (doseq [alias '[list/length list/append list/map]]
      (let [declaration (environment/declaration
                         environment (environment/resolve-id environment alias))
            recursor-id (environment/resolve-id environment 'data/List.rec)
            checked (kernel/check environment
                                  (:rainbow/value declaration)
                                  (:rainbow/type declaration)
                                  (set (:rainbow/universes declaration)))]
        (is (= :reducible (:rainbow/transparency declaration)))
        (is (contains? (:rainbow/dependencies declaration) recursor-id)
            (str alias " must recurse only through List.rec"))
        (is (= :checked (:status checked)) (str alias " must independently recheck"))))))

(deftest length-append-and-map-compute-on-concrete-lists
  (let [{:keys [environment]} @checked-corpus
        {:keys [level nat zero successor one two nil-term cons
                singleton-zero singleton-one zero-one]}
        (core-terms environment)
        length (inductive/constant environment 'list/length [level])
        append (inductive/constant environment 'list/append [level])
        map-list (inductive/constant environment 'list/map [level level])
        length-result (inductive/apply* length nat zero-one)
        append-result (inductive/apply* append nat singleton-zero singleton-one)
        map-result (inductive/apply* map-list nat nat successor zero-one)
        expected-map (inductive/apply* cons nat one
                                       (inductive/apply* cons nat two nil-term))]
    (is (= two (:term (kernel/normalize environment length-result))))
    (is (= zero-one (:term (kernel/normalize environment append-result))))
    (is (= expected-map (:term (kernel/normalize environment map-result))))))

(deftest all-eight-list-theorems-recheck-and-two-use-induction
  (let [{:keys [environment results]} @checked-corpus
        induction-results
        (filter #(some #{:induction}
                       (map :event/tactic (get-in % [:result :proof :proof/history])))
                results)]
    (is (= 8 (count results)))
    (is (= '#{list/append-nil-right list/map-identity}
           (set (map :name induction-results))))
    (doseq [{:keys [name declaration]} results]
      (let [persisted (environment/declaration
                       environment (environment/resolve-id environment name))
            checked (kernel/check environment
                                  (:rainbow/value persisted)
                                  (:rainbow/type persisted)
                                  (set (:rainbow/universes persisted)))]
        (is (= (:rainbow/id declaration) (:rainbow/id persisted)))
        (is (= :checked (:status checked)) (str name " must independently recheck"))
        (is (= #{} (kernel/axioms environment name)) (str name " must be axiom-free"))))))

(deftest unrestricted-self-recursion-is-rejected
  (let [{:keys [environment]} @checked-corpus
        result (list-data/nontermination-attempt environment)]
    (is (= :rejected (:status result)))
    (is (= :kernel/invalid-declaration-value
           (get-in result [:error :error/category])))
    (is (= :kernel/unknown-constant
           (get-in result [:error :cause :error :error/category])))
    (is (nil? (environment/resolve-id environment 'list/nonterminating-loop)))))

(deftest list-corpus-persists-and-replays-in-a-fresh-jvm
  (let [path "artifacts/day9/environment.edn"
        replay (java-command "-m" "rainbow.data.list" "replay" path)
        report-a (java-command "-m" "rainbow.data.list")
        report-b (java-command "-m" "rainbow.data.list")]
    (is (zero? (:exit replay)) (:err replay))
    (is (.contains ^String (:out replay) ":status :replayed"))
    (is (zero? (:exit report-a)) (:err report-a))
    (is (zero? (:exit report-b)) (:err report-b))
    (is (= (:out report-a) (:out report-b)))))
