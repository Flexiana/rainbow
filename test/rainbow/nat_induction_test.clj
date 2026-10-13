(ns rainbow.nat-induction-test
  (:require [clojure.java.shell :as shell]
            [clojure.test :refer :all]
            [rainbow.history.nat-induction :as nat-induction]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

(def checked-corpus (delay (nat-induction/build)))

(defn java-command [& arguments]
  (apply shell/sh
         (str (System/getProperty "java.home") "/bin/java")
         "-cp" (System/getProperty "java.class.path")
         "clojure.main"
         arguments))

(defn reflexive-target [terms]
  (term/pi-term (:nat terms)
                (nat-induction/equality-type terms (term/bound 0) (term/bound 0))))

(deftest induction-exposes-zero-and-successor-cases
  (let [environment (nat-induction/base-environment)
        terms (nat-induction/nat-terms environment)
        introduced (tactic/run
                    (:state (proof/start environment (reflexive-target terms)))
                    (tactic/intro 'n))
        induced (tactic/run (:state introduced) (tactic/induction [:bound 0]))
        [zero-case successor-case] (:goals induced)]
    (is (= :progress (:status induced)))
    (is (= {:event/tactic :induction
            :event/expression [:bound 0]
            :event/cases 2}
           (:event induced)))
    (is (= 2 (count (:goals induced))))
    (is (= :app (first (:goal/target zero-case))))
    (is (= :pi (first (:goal/target successor-case))))
    (is (= :pi (first (nth (:goal/target successor-case) 2))))
    (is (= [[0 0] [0 1]] (mapv :goal/path (:goals induced))))))

(deftest induction-hypothesis-rewrites-the-successor-case
  (let [environment (nat-induction/base-environment)
        result (nat-induction/prove-recursor-identity environment
                                             (nat-induction/nat-terms environment))
        tactics (mapv :event/tactic (get-in result [:proof :proof/history]))]
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (= [:intro :induction :exact :intro :intro :rewrite :exact] tactics))
    (is (= :backward
           (get-in result [:proof :proof/history 5 :event/direction])))
    (is (= #{} (get-in result [:proof :proof/axioms])))))

(deftest all-eight-nat-theorems-recheck-and-are-axiom-free
  (let [{:keys [environment results]} @checked-corpus]
    (is (= 8 (count results)))
    (doseq [{:keys [name declaration]} results]
      (let [persisted (environment/declaration
                       environment
                       (environment/resolve-id environment name))
            checked (kernel/check environment
                                  (:rainbow/value persisted)
                                  (:rainbow/type persisted))]
        (is (= (:rainbow/id declaration) (:rainbow/id persisted)))
        (is (= :checked (:status checked)) (str name " must independently recheck"))
        (is (= #{} (kernel/axioms environment name)) (str name " must be axiom-free"))))))

(deftest induction-on-a-non-inductive-local-fails-without-changing-state
  (let [environment (nat-induction/base-environment)
        sort-zero [:sort [:zero]]
        target (term/pi-term sort-zero sort-zero)
        introduced (tactic/run (:state (proof/start environment target))
                               (tactic/intro 'A))
        state (:state introduced)
        result (tactic/run state (tactic/induction [:bound 0]))]
    (is (= :failure (:status result)))
    (is (= :tactic/not-inductive
           (get-in result [:failure :failure/category])))
    (is (= state (:state result)))))

(deftest nat-corpus-persists-and-replays-in-a-fresh-jvm
  (let [path "artifacts/day8/environment.edn"
        replay (java-command "-m" "rainbow.history.nat-induction" "replay" path)
        report-a (java-command "-m" "rainbow.history.nat-induction")
        report-b (java-command "-m" "rainbow.history.nat-induction")]
    (is (zero? (:exit replay)) (:err replay))
    (is (.contains ^String (:out replay) ":status :replayed"))
    (is (zero? (:exit report-a)) (:err report-a))
    (is (zero? (:exit report-b)) (:err report-b))
    (is (= (:out report-a) (:out report-b)))))
