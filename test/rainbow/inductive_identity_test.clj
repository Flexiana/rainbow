(ns rainbow.inductive-identity-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.kernel :as kernel]
            [rainbow.environment :as environment]
            [rainbow.term :as term]))

(def prop [:sort [:zero]])
(defn- pi [a b] [:pi a b :explicit])
(defn- lam [a b] [:lam a b :explicit])
(defn- app [f & args] (reduce #(vector :app %1 %2) f args))
(defn- constant [env alias] [:const (environment/resolve-id env alias) []])

(defn- block-spec [alias constructor result-name names]
  (let [[x y value] names]
    {:block/schema-version 1 :block/alias alias :block/universes [] :block/parameters []
     :block/sort-level [:succ [:zero]]
     :block/constructors
     [{:constructor/alias constructor
       :constructor/fields
       [{:field/name 'function
         :field/type [:pi [[x prop]]
                      [:pi [[y prop]]
                       [:pi [[value [:var x]]] [:var result-name]]]]}]}]}))

(def identity-spec (block-spec 'identity/Box 'identity/make 'X '[X Y x]))
(def cast-spec (block-spec 'cast/Box 'cast/make 'Y '[X Y x]))

(defn- add [env alias kind type value]
  (kernel/add-declaration env
                         {:rainbow/kind kind :rainbow/aliases #{alias}
                          :rainbow/universes [] :rainbow/type type :rainbow/value value
                          :rainbow/transparency :reducible
                          :rainbow/dependencies (into (term/constants type) (term/constants value))}))

(deftest nested-binder-identity-distinguishes-outer-and-inner-references
  (is (not= (kernel/inductive-block-id identity-spec)
            (kernel/inductive-block-id cast-spec)))
  (is (= (kernel/inductive-block-id identity-spec)
         (kernel/inductive-block-id
          (block-spec 'renamed/Box 'renamed/make 'P '[P Q value]))))
  ;; The same distinction must survive when the nested Pi occurs in a domain.
  (let [wrap (fn [spec]
               (update-in spec [:block/constructors 0 :constructor/fields 0 :field/type]
                          #(vector :pi [['argument %]] prop)))]
    (is (not= (kernel/inductive-block-id (wrap identity-spec))
              (kernel/inductive-block-id (wrap cast-spec))))))

(deftest a-second-block-cannot-turn-identity-into-an-axiom-free-proof-of-false
  (let [first-block (kernel/add-inductive-block (environment/empty-environment) identity-spec)
        first-env (:environment first-block)
        identity-field (lam prop (lam prop (lam [:bound 1] [:bound 0])))
        boxed (add first-env 'identity/boxed :definition (constant first-env 'identity/Box)
                   (app (constant first-env 'identity/make) identity-field))
        second-block (kernel/add-inductive-block (:environment boxed) cast-spec)
        env (:environment second-block)
        identity-type (second (:rainbow/type (environment/declaration env (environment/resolve-id env 'identity/make))))
        target-type (second (:rainbow/type
                             (environment/declaration env (environment/resolve-id env 'cast/make))))
        bogus-cast (app [:const (environment/resolve-id env 'cast/Box.rec) [[:zero]]]
                        (lam (constant env 'cast/Box) target-type)
                        (lam target-type [:bound 0])
                        (constant env 'identity/boxed))
        true-type (pi prop (pi [:bound 0] [:bound 1]))
        false-type (pi prop [:bound 0])
        true-proof (lam prop (lam [:bound 0] [:bound 0]))
        bogus-proof (app bogus-cast true-type false-type true-proof)
        installed (add env 'cast/false :theorem false-type bogus-proof)]
    (is (= :accepted (:status first-block)))
    (is (= :accepted (:status boxed)))
    (is (= :accepted (:status second-block)))
    (is (not= (environment/resolve-id env 'identity/Box)
              (environment/resolve-id env 'cast/Box)))
    (is (= :checked (:status (kernel/check env identity-field identity-type))))
    (is (= :checked (:status (kernel/check env (constant env 'identity/boxed)
                                           (constant env 'identity/Box)))))
    (is (= :rejected (:status (kernel/check env bogus-cast target-type))))
    (is (= :rejected (:status (kernel/check env bogus-proof false-type))))
    (is (= :rejected (:status installed)))
    (is (nil? (environment/resolve-id env 'cast/false)))))
