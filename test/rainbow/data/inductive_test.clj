(ns rainbow.data.inductive-test
  (:require [clojure.java.shell :as shell]
            [clojure.test :refer :all]
            [rainbow.data.inductive :as inductive]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.prelude :as prelude]))

(def checked-environment (delay (inductive/build-environment)))

(defn java-command [& arguments]
  (apply shell/sh
         (str (System/getProperty "java.home") "/bin/java")
         "-cp" (System/getProperty "java.class.path")
         "clojure.main"
         arguments))

(deftest four-inductive-blocks-and-members-type-check
  (let [env @checked-environment]
    (is (= 4 (count (:rainbow.environment/blocks env))))
    (is (= 62 (count (:rainbow.environment/declarations env))))
    (doseq [alias '[data/Bool data/Nat data/Product data/Sum]]
      (is (= #{} (kernel/axioms env alias))))
    (doseq [block-id (:rainbow.environment/block-order env)
            member-id (:block/member-ids (environment/block env block-id))]
      (let [member (environment/declaration env member-id)
            inferred (kernel/infer env (:rainbow/type member)
                                   (set (:rainbow/universes member)))]
        (is (contains? #{:inductive :constructor :recursor} (:rainbow/kind member)))
        (is (= :checked (:status inferred))
            (str (:rainbow/aliases member) " type must check"))))))

(deftest every-recursor-computes-and-yields-a-checked-equality-proof
  (let [env @checked-environment]
    (doseq [{:keys [name expression expected]} (inductive/computation-cases env)]
      (is (= expected (:term (kernel/normalize env expression)))
          (str name " must iota-reduce"))
      (let [declaration (environment/declaration env (environment/resolve-id env name))
            checked (kernel/check env (:rainbow/value declaration) (:rainbow/type declaration))]
        (is (= :checked (:status checked)) (str name " proof must replay"))
        (is (= #{} (kernel/axioms env name)))))))

(deftest iota-reduction-obeys-kernel-fuel
  (let [env @checked-environment
        expression (:expression (first (inductive/computation-cases env)))
        result (kernel/normalize env expression {:reductions 0})]
    (is (= :resource-limit (:status result)))
    (is (= :kernel/resource-limit (get-in result [:error :error/category])))))

(deftest non-strict-positivity-and-forged-members-are-rejected
  (let [negative (assoc-in inductive/nat-spec
                           [:block/constructors 1 :constructor/fields 0 :field/type]
                           [:pi [:self] [:var 'predecessor]])
        negative-result (kernel/add-inductive-block (inductive/base-environment) negative)
        forged-result (kernel/add-inductive-block
                       (inductive/base-environment)
                       (assoc inductive/bool-spec :rainbow/id "sha256:forged"))
        env @checked-environment
        member (environment/declaration env
                                        (environment/resolve-id env 'data/Bool))
        standalone (kernel/add-declaration (inductive/base-environment) member)]
    (is (= :rejected (:status negative-result)))
    (is (= :kernel/non-strictly-positive
           (get-in negative-result [:error :error/category])))
    (is (= :rejected (:status forged-result)))
    (is (= :kernel/forged-inductive-block-id
           (get-in forged-result [:error :error/category])))
    (is (= :rejected (:status standalone)))
    (is (= :kernel/standalone-block-member
           (get-in standalone [:error :error/category])))))

(deftest block-identity-is-alpha-and-alias-invariant
  (let [renamed-bool (-> inductive/bool-spec
                         (assoc :block/alias 'renamed/Truth)
                         (assoc-in [:block/constructors 0 :constructor/alias] 'renamed/no)
                         (assoc-in [:block/constructors 1 :constructor/alias] 'renamed/yes))
        renamed-product
        {:block/schema-version 1
         :block/alias 'renamed/Pair
         :block/universes ['x 'y]
         :block/parameters
         [{:parameter/name 'X :parameter/type [:sort [:param 'x]]}
          {:parameter/name 'Y :parameter/type [:sort [:param 'y]]}]
         :block/sort-level [:max [:param 'x] [:param 'y]]
         :block/constructors
         [{:constructor/alias 'renamed/mk
           :constructor/fields [{:field/name 'left-value :field/type [:var 'X]}
                                {:field/name 'right-value :field/type [:var 'Y]}]}]}]
    (is (= (kernel/inductive-block-id inductive/bool-spec)
           (kernel/inductive-block-id renamed-bool)))
    (is (= (kernel/inductive-block-id inductive/product-spec)
           (kernel/inductive-block-id renamed-product)))
    (is (not= (kernel/inductive-block-id inductive/bool-spec)
              (kernel/inductive-block-id
               (update inductive/bool-spec :block/constructors conj
                       {:constructor/alias 'data/maybe
                        :constructor/fields []}))))))

(deftest dependent-parameters-and-fields-are-checked-and-alpha-invariant
  (let [added (kernel/add-inductive-block (inductive/base-environment)
                                          prelude/subtype-spec)
        renamed
        {:block/schema-version 1
         :block/alias 'renamed/Subset
         :block/universes ['v]
         :block/parameters
         [{:parameter/name 'X :parameter/type [:sort [:param 'v]]}
          {:parameter/name 'condition
           :parameter/type
           [:pi [['candidate [:var 'X]]] [:sort [:zero]]]}]
         :block/sort-level [:max [:succ [:zero]] [:param 'v]]
         :block/constructors
         [{:constructor/alias 'renamed/include
           :constructor/fields
           [{:field/name 'element :field/type [:var 'X]}
            {:field/name 'evidence
             :field/type [:app [:var 'condition] [:var 'element]]}]}]}
        forward-reference
        (assoc-in prelude/subtype-spec
                  [:block/constructors 0 :constructor/fields 0 :field/type]
                  [:var 'property])
        rejected (kernel/add-inductive-block (inductive/base-environment)
                                              forward-reference)]
    (is (= :accepted (:status added)) (pr-str added))
    (is (= (kernel/inductive-block-id prelude/subtype-spec)
           (kernel/inductive-block-id renamed)))
    (doseq [member-id (get-in added [:block :block/member-ids])]
      (let [member (environment/declaration (:environment added) member-id)]
        (is (= :checked
               (:status (kernel/infer (:environment added)
                                      (:rainbow/type member)
                                      (set (:rainbow/universes member))))))))
    (is (= :rejected (:status rejected)))
    (is (= :kernel/unknown-block-variable
           (get-in rejected [:error :error/category])))))

(deftest persisted-blocks-replay-and-hash-identically-in-fresh-jvms
  (let [path "artifacts/day7/environment.edn"
        replays (repeatedly 3 #(java-command "-m" "rainbow.data.inductive" "replay" path))
        reports (repeatedly 3 #(java-command "-m" "rainbow.data.inductive"))]
    (is (every? #(zero? (:exit %)) replays))
    (is (= 1 (count (set (map :out replays)))))
    (is (every? #(zero? (:exit %)) reports))
    (is (= 1 (count (set (map :out reports)))))))
