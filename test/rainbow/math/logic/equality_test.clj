(ns rainbow.math.logic.equality-test
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.test :refer :all]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.equality :as equality]
            [rainbow.persistence :as persistence]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]))

(defn java-command [& arguments]
  (apply shell/sh
         (str (System/getProperty "java.home") "/bin/java")
         "-cp" (System/getProperty "java.class.path")
         "clojure.main"
         arguments))

(deftest ten-equality-theorems-are-axiom-free-and-kernel-checked
  (let [environment (equality/build-environment)]
    (is (= 10 (count equality/theorem-specs)))
    (is (= 39 (count (:rainbow.environment/declarations environment))))
    (doseq [{:keys [name]} equality/theorem-specs]
      (let [id (environment/resolve-id environment name)
            declaration (environment/declaration environment id)
            checked (kernel/check environment
                                  (:rainbow/value declaration)
                                  (:rainbow/type declaration)
                                  (set (:rainbow/universes declaration)))]
        (is (= :checked (:status checked)) (str name " must replay"))
        (is (= #{} (kernel/axioms environment name)) (str name " must be axiom-free"))))))

(deftest invalid-substitution-is-rejected
  (let [environment (equality/build-environment)
        bad {:name 'equality/invalid-substitution
             :universes ['u]
             :type (equality/forall [['A equality/sort-u] ['x 'A] ['y 'A]
                                     ['h (equality/eq 'A 'x 'y)]
                                     ['P (equality/arrow 'A 'Prop)]
                                     ['px (equality/app 'P 'x)]]
                                    (equality/app 'P 'y))
             ;; Returning px ignores both h and the changed endpoint.
             :value (equality/lam [['A equality/sort-u] ['x 'A] ['y 'A]
                                   ['h (equality/eq 'A 'x 'y)]
                                   ['P (equality/arrow 'A 'Prop)]
                                   ['px (equality/app 'P 'x)]]
                                  'px)}
        result (equality/add-spec environment bad)]
    (is (= :rejected (:status result)))
    (is (= :kernel/invalid-declaration-value
           (get-in result [:error :error/category])))))

(deftest reflexivity-tactic-reconstructs-a-kernel-proof
  (let [environment (equality/build-environment)
        type-surface (equality/forall
                      [['A equality/sort-u] ['x 'A]]
                      (equality/eq 'A 'x 'x))
        target (:term (elaborate/core-expression environment type-surface))
        started (proof/start environment target {:universes ['u]})
        introduced (tactic/run (:state started)
                               (tactic/repeat (tactic/intro) {:max 2}))
        result (tactic/run (:state introduced) (tactic/reflexivity))]
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (= #{} (get-in result [:proof :proof/axioms])))))

(deftest equality-corpus-persists-and-replays-in-a-fresh-jvm
  (let [path (.getAbsolutePath (java.io.File/createTempFile "rainbow-equality-" ".edn"))
        environment (equality/build-environment)
        save (persistence/save-environment! environment path)
        replay (java-command "-m" "rainbow.math.logic.equality" "replay" path)]
    (try
      (is (= :saved (:status save)))
      (is (zero? (:exit replay)) (:err replay))
      (is (.contains ^String (:out replay) ":status :replayed"))
      (finally (.delete (io/file path))))))

(deftest explicit-term-elaboration-rejects-unknown-constants
  (let [result (elaborate/core-expression (equality/build-environment)
                                          [:const 'equality/does-not-exist []])]
    (is (= :rejected (:status result)))
    (is (= :elaborate/unknown-constant (get-in result [:error :error/category])))))
