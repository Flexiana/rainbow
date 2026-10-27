(ns rainbow.kernel-block-axioms-test
  "Claim integrity (A3): a block member's
  type may mention an axiom (a postulated type as a field), and every declaration built on
  the member must then report that axiom."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.data.inductive :as inductive]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def type1 [:sort [:succ [:zero]]])

(defn- with-postulate []
  ;; an axiom T : Sort 1 -- a type nobody constructed
  (let [result (kernel/add-declaration
                (inductive/base-environment)
                {:rainbow/kind :axiom :rainbow/aliases #{'test/T} :rainbow/universes []
                 :rainbow/type type1 :rainbow/value nil :rainbow/transparency :opaque
                 :rainbow/dependencies #{} :rainbow/provenance {:origin :native :producer :test}
                 :rainbow/schema-version 1})]
    (assert (= :accepted (:status result)) (pr-str result))
    [(:environment result) (get-in result [:declaration :rainbow/id])]))

(defn- wrap-spec [t-id]
  {:block/schema-version 1 :block/alias 'test/Wrap :block/universes [] :block/parameters []
   :block/sort-level [:succ [:zero]]
   :block/constructors [{:constructor/alias 'test/wrap
                         :constructor/fields [{:field/name 'x :field/type [:const t-id []]}]}]})

(deftest members-whose-types-mention-an-axiom-report-it
  (let [[env t-id] (with-postulate)
        added (kernel/add-inductive-block env (wrap-spec t-id))
        env (:environment added)]
    (is (= :accepted (:status added)) (pr-str added))
    ;; the field type T appears in the constructor's and the recursor's types, not in Wrap's (Sort 1)
    (doseq [alias '[test/wrap test/Wrap.rec]]
      (is (= #{t-id} (kernel/axioms env alias)) (str alias)))
    (is (= #{} (kernel/axioms env 'test/Wrap)))
    ;; a definition that uses the constructor inherits the axiom through it
    (let [wrap-id (environment/resolve-id env 'test/wrap)
          wrap-type [:const (environment/resolve-id env 'test/Wrap) []]
          t-type [:const t-id []]
          ;; rewrap x = wrap x : T -> Wrap, through the constructor
          user {:rainbow/kind :definition :rainbow/aliases #{'test/rewrap} :rainbow/universes []
                :rainbow/type [:pi t-type wrap-type :explicit]
                :rainbow/value [:lam t-type [:app [:const wrap-id []] [:bound 0]] :explicit]
                :rainbow/transparency :reducible
                :rainbow/dependencies #{t-id wrap-id (environment/resolve-id env 'test/Wrap)}
                :rainbow/provenance {:origin :native :producer :test} :rainbow/schema-version 1}
          result (kernel/add-declaration env user)]
      (is (= :accepted (:status result)) (pr-str result))
      (is (= #{t-id} (kernel/axioms (:environment result) 'test/rewrap)))
      (is wrap-id))))

(deftest axiom-free-blocks-still-report-none
  (let [env (inductive/build-environment)]
    (doseq [alias '[data/Bool data/true data/Nat data/succ data/Nat.rec data/Product data/Sum.rec]]
      (is (= #{} (kernel/axioms env alias)) (str alias)))))
