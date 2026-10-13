(ns rainbow.lean-bridge-test
  (:require [clojure.java.shell :as shell]
            [clojure.test :refer :all]
            [rainbow.data.inductive :as inductive]
            [rainbow.environment :as environment]
            [rainbow.foreign.lean :as lean]
            [rainbow.graph :as graph]
            [rainbow.kernel :as kernel]))

(def checked-import (delay (lean/build)))

(defn java-command [& arguments]
  (apply shell/sh
         (str (System/getProperty "java.home") "/bin/java")
         "-cp" (System/getProperty "java.class.path")
         "clojure.main"
         arguments))

(deftest pinned-neutral-fixture-has-the-supported-logic-nat-closure
  (let [fixture (lean/load-neutral "artifacts/day12/lean-neutral.edn")]
    (is (= 1 (:foreign/schema-version fixture)))
    (is (= :lean (:foreign/system fixture)))
    (is (= lean/pinned-version (:foreign/version fixture)))
    (is (= lean/pinned-commit (:foreign/commit fixture)))
    (is (= 8 (count (:foreign/declarations fixture))))
    (is (= {:definition 6 :theorem 2}
           (frequencies (map :foreign/kind (:foreign/declarations fixture)))))
    (is (every? false? (map :foreign/unsafe? (:foreign/declarations fixture))))))

(deftest every-import-rechecks-and-retains-foreign-provenance
  (let [{:keys [status environment objects]} @checked-import]
    (is (= :imported status))
    (is (= 8 (count objects)))
    (is (= 90 (count (:rainbow.environment/declarations environment))))
    (doseq [object objects]
      (let [id (:foreign/native-declaration-id object)
            declaration (environment/declaration environment id)
            checked (kernel/check environment
                                  (:rainbow/value declaration)
                                  (:rainbow/type declaration)
                                  (set (:rainbow/universes declaration)))]
        (is (= :foreign-declaration (:rainbow/kind object)))
        (is (= :accepted (get-in object [:foreign/check :status])))
        (is (= :foreign (get-in declaration [:rainbow/provenance :origin])))
        (is (= :lean (get-in declaration [:rainbow/provenance :foreign/system])))
        (is (= :checked (:status checked)) (:foreign/name object))
        (is (= #{} (kernel/axioms environment id)))))))

(deftest imported-nat-successor-computes-over-native-nat
  (let [{:keys [environment]} @checked-import
        successor (inductive/constant
                   environment
                   (lean/foreign-alias "RainbowFixture.natSuccessor") [])
        zero (inductive/constant environment 'data/zero [])
        native-successor (inductive/constant environment 'data/succ [])
        expression (inductive/apply* successor zero)]
    (is (= (inductive/apply* native-successor zero)
           (:term (kernel/normalize environment expression))))))

(deftest unsupported-toolchain-unsafe-and-expression-forms-reject-explicitly
  (let [environment (lean/base-environment)
        fixture (lean/load-neutral "artifacts/day12/lean-neutral.edn")
        wrong-toolchain (lean/import-fixture environment
                                             (assoc fixture :foreign/version "4.29.1"))
        unsafe-fixture (assoc-in fixture [:foreign/declarations 0 :foreign/unsafe?] true)
        unsafe-result (lean/import-fixture environment unsafe-fixture)
        unsupported-fixture
        (assoc-in fixture [:foreign/declarations 0 :foreign/value]
                  [:unsupported :literal "NatLit 1"])
        unsupported-result (lean/import-fixture environment unsupported-fixture)]
    (is (= :foreign/toolchain-mismatch
           (get-in wrong-toolchain [:error :error/category])))
    (is (= :foreign/unsafe-declaration
           (get-in unsafe-result [:error :error/category])))
    (is (= :foreign/unsupported-expression
           (get-in unsupported-result [:error :error/category])))
    (is (= [:foreign/declarations "RainbowFixture.polymorphicIdentity"
            :foreign/value]
           (get-in unsupported-result [:error :path])))))

(deftest raw-foreign-graph-retains-unsupported-and-unsafe-data-without-native-import
  (let [fixture {:foreign/schema-version 1
                 :foreign/system :lean
                 :foreign/version lean/pinned-version
                 :foreign/commit lean/pinned-commit
                 :foreign/declarations
                 [{:foreign/name "Foreign.base"
                   :foreign/kind :axiom
                   :foreign/universes []
                   :foreign/type [:unsupported :opaque-sort]
                   :foreign/value nil
                   :foreign/unsafe? true
                   :foreign/source {:module "Foreign" :line 10}}
                  {:foreign/name "Foreign.user"
                   :foreign/kind :definition
                   :foreign/universes []
                   :foreign/type [:const "Foreign.base" []]
                   :foreign/value [:unsupported-body
                                   [:const "External.missing" []]]
                   :foreign/unsafe? false}]}
        result (lean/ingest-foreign-graph fixture)
        value (:graph result)
        objects (:objects result)
        base (first objects)
        user (second objects)
        base-id (graph/foreign-object-id base)
        user-id (graph/foreign-object-id user)
        missing-id (graph/foreign-reference-id
                    :lean lean/pinned-version lean/pinned-commit
                    "External.missing")]
    (is (= :ingested (:status result)))
    (is (= :valid (:status (graph/validate value))))
    (is (= 2 (:object-count result)))
    (is (true? (:foreign/unsafe? base)))
    (is (not (contains? user :foreign/native-declaration-id)))
    (is (= #{base-id missing-id} (graph/dependencies value user-id)))
    (is (= :foreign-reference
           (get-in value [:graph/nodes missing-id :graph.node/kind])))
    (is (= (:graph/id result)
           (:graph/id (lean/ingest-foreign-graph
                       (update fixture :foreign/declarations
                               #(vec (reverse %)))))))))

(deftest raw-foreign-graph-rejects-duplicate-names
  (let [fixture (lean/load-neutral "artifacts/day12/lean-neutral.edn")
        duplicate (update fixture :foreign/declarations conj
                          (first (:foreign/declarations fixture)))
        result (lean/ingest-foreign-graph duplicate)]
    (is (= :rejected (:status result)))
    (is (= :graph/duplicate-foreign-name
           (get-in result [:error :error/category])))))

(deftest explicit-lean-axiom-is-visible-in-provenance-and-axiom-closure
  (let [environment (lean/base-environment)
        fixture (lean/load-neutral "artifacts/day12/lean-neutral.edn")
        axiom {:foreign/name "RainbowFixture.assumedProposition"
               :foreign/kind :axiom
               :foreign/universes []
               :foreign/type [:sort [:zero]]
               :foreign/value nil
               :foreign/unsafe? false}
        result (lean/import-fixture environment
                                    (update fixture :foreign/declarations conj axiom))
        object (last (:objects result))
        id (:foreign/native-declaration-id object)]
    (is (= :imported (:status result)))
    (is (= :axiom (:foreign/kind object)))
    (is (true? (get-in object [:foreign/provenance :axiom?])))
    (is (= #{id} (kernel/axioms (:environment result) id)))))

(deftest imported-environment-replays-in-a-fresh-jvm
  (let [path "artifacts/day12/environment.edn"
        replay (java-command "-m" "rainbow.foreign.lean" "replay" path)
        report-a (java-command "-m" "rainbow.foreign.lean")
        report-b (java-command "-m" "rainbow.foreign.lean")]
    (is (zero? (:exit replay)) (:err replay))
    (is (.contains ^String (:out replay) ":status :replayed"))
    (is (zero? (:exit report-a)) (:err report-a))
    (is (zero? (:exit report-b)) (:err report-b))
    (is (= (:out report-a) (:out report-b)))))
