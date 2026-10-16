(ns rainbow.bundle-shared-test
  "The shared bundle encoding: the same declarations written as a DAG. Decoding must
  give back exactly the plain bundle, a shared bundle is checked like a plain one, and
  anything tampered or malformed is refused -- by the decoder or by the kernel, never
  accepted."
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]
            [rainbow.bundle.shared :as shared]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.data.inductive :as inductive]
            [rainbow.environment :as environment]
            [rainbow.history.direct-term-corpus :as corpus]
            [rainbow.kernel :as kernel]
            [rainbow.main :as main]))

(def ^:private empty-env (environment/empty-environment))
(def ^:private checked-env (delay (corpus/build-environment)))

(defn- plain []
  (main/proof-bundle {:checkpoint "test-base" :modules []
                      :base-env empty-env :env @checked-env
                      :claims (map :name corpus/proofs)}))

(defn- round-trip [x] (edn/read-string (pr-str x)))

(defmacro ^:private on-test-base [& body]
  `(with-redefs [checkpoint/load-checkpoint (fn [_#] {:status :replayed :environment empty-env})]
     ~@body))

(deftest decoding-gives-back-the-plain-bundle
  (let [b (plain) s (shared/encode b)]
    (is (= 3 (:rainbow.bundle/schema-version s)))
    (is (= b (shared/decode s)))
    (is (= b (shared/decode (round-trip s))) "through EDN, as written to a file")
    (is (= (map environment/declaration-id (:declarations b))
           (map environment/declaration-id (:declarations (shared/decode (round-trip s))))))
    (is (< (count (pr-str s)) (count (pr-str b))))))

(deftest block-bundles-round-trip-too
  (let [block (kernel/add-inductive-block @checked-env inductive/bool-spec)
        b (main/proof-bundle {:checkpoint "block-base" :modules [] :base-env @checked-env
                              :env (:environment block) :claims []})
        b (assoc b :claims {})]
    (is (= 2 (:rainbow.bundle/schema-version b)))
    (is (= b (shared/decode (round-trip (shared/encode b)))))))

(deftest a-shared-bundle-is-checked-like-the-plain-one
  (on-test-base
   (let [plain-result (main/check-bundle (round-trip (plain)))
         shared-result (main/check-bundle (round-trip (shared/encode (plain))))]
     (is (true? (:ok? plain-result)))
     (is (true? (:ok? shared-result)) (pr-str shared-result))
     (is (= (:claims plain-result) (:claims shared-result))))))

(deftest tampering-is-refused-by-the-kernel
  (on-test-base
   (let [s (shared/encode (plain))
         ;; one variable in one proof now refers to a different binder
         i (first (keep-indexed (fn [i n] (when (= :bound (first n)) i)) (:terms s)))
         tampered (update-in s [:terms i 1] inc)]
     (is (not= s tampered))
     (is (false? (:ok? (main/check-bundle (round-trip tampered))))))))

(deftest malformed-tables-are-refused-before-the-kernel
  (on-test-base
   (let [s (shared/encode (plain))
         app (first (keep-indexed (fn [i n] (when (= :app (first n)) i)) (:terms s)))
         cases {"a forward reference" (assoc-in s [:terms app 1] (inc app))
                "a constant out of range" (assoc-in s [:terms 0] [:const 999999 []])
                "an unknown tag" (assoc-in s [:terms 0] [:not-a-tag 1])
                "terms that are not a vector" (assoc s :terms {})
                "a payload schema that does not exist" (assoc s :rainbow.bundle/payload-schema 7)
                "duplicate constants" (update s :constants #(conj % (first %)))}]
     (doseq [[what bad] cases]
       (testing what
         (let [r (main/check-bundle (round-trip bad))]
           (is (false? (:ok? r)))
           (is (re-find #"malformed shared bundle" (str (:error r))) (:error r))))))))

(deftest literals-are-shared-and-checked-like-other-leaves
  (let [b (assoc-in (plain) [:declarations 0 :rainbow/type] [:pi [:sort [:zero]] [:nat 12345678901234567890] :explicit])
        s (shared/encode b)]
    (is (= b (shared/decode (round-trip s))))
    (is (some #(= [:nat 12345678901234567890] %) (:terms s)))
    (doseq [bad [[:nat -1] [:nat 1.5] [:nat]]]
      (let [i (first (keep-indexed (fn [i n] (when (= :nat (first n)) i)) (:terms s)))]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"malformed shared bundle"
                              (shared/decode (assoc-in s [:terms i] bad))))))))
