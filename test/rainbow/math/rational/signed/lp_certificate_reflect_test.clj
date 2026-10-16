(ns rainbow.math.rational.signed.lp-certificate-reflect-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.lp-certificate-reflect :as reflection]))

(def ^:private U [:param 'u])
(def ^:private L [:succ [:zero]])
(defn- c [alias] (f/const* alias []))
(defn- app [g & args] (apply f/app g args))
(def ^:private Q (c 'signed/SignedRational))
(def ^:private N (c 'data/Nat))
(def ^:private Bool (c 'data/Bool))
(defn- eq-true [v] (f/equality L Bool v (c 'data/true)))
(defn- list-type [level T] (app (f/const* 'data/List [[:succ level]]) T))
(defn- sum [level T g xs] (app (f/const* 'signed/map-sum [level]) T g xs))
(defn- all-le [level T g h xs] (app (f/const* 'signed/all-at-most [level]) T g h xs))
(defn- mul [a b] (app (c 'signed/multiply) a b))
(defn- le [a b] (app (c 'signed/at-most) a b))
(defn- zero-fn [T] (f/lam [['unused T]] (c 'signed/zero)))
(defn- rows-of [level I J M v cols]
  (f/lam [['i I]]
         (sum level J (f/lam [['j J]] (mul (app (app M 'i) 'j) (app v 'j))) cols)))
(defn- objective [level J costs v cols]
  (sum level J (f/lam [['j J]] (mul (app costs 'j) (app v 'j))) cols))
(defn- conclusion [level I J M b costs plan rows cols]
  (f/forall [['alternative (f/arrow J Q)]
             ['feasible (all-le level I (rows-of level I J M 'alternative cols) b rows)]
             ['nonnegative (all-le level J (zero-fn J) 'alternative cols)]]
            (le (objective level J costs 'alternative cols)
                (objective level J costs plan cols))))

(def ^:private checked
  (delay
    (let [base (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (assert (= :replayed (:status base)))
      (reflection/extend-environment (:environment base)))))
(defn- core [surface]
  (let [result (elaborate/core-expression @checked surface)]
    (assert (= :elaborated (:status result)) (pr-str result))
    (:term result)))
(defn- normal [surface]
  (let [result (kernel/normalize @checked (core surface))]
    (assert (= :normalized (:status result)) (pr-str result))
    (:term result)))

;; Restated without referring to the implementation's bindings, clauses or specs.
(def ^:private frozen-types
  (let [T [:sort [:succ U]]
        fs [['Index T] ['lower (f/arrow 'Index Q)] ['upper (f/arrow 'Index Q)]
            ['indices (list-type U 'Index)]]
        all-decision (app (f/const* 'lp/all-at-most-decide [U])
                          'Index 'lower 'upper 'indices)
        args ['I 'J 'matrix 'bounds 'costs 'plan 'prices 'row-list 'col-list]
        bs [['I T] ['J T] ['matrix (f/arrow 'I (f/arrow 'J Q))]
            ['bounds (f/arrow 'I Q)] ['costs (f/arrow 'J Q)]
            ['plan (f/arrow 'J Q)] ['prices (f/arrow 'I Q)]
            ['row-list (list-type U 'I)] ['col-list (list-type U 'J)]]]
    {'lp/all-at-most-decide (f/forall fs Bool)
     'lp/all-at-most-decide-sound
     (f/forall (conj fs ['accepted (eq-true all-decision)])
               (all-le U 'Index 'lower 'upper 'indices))
     'lp/certificate-check (f/forall bs Bool)
     'lp/certificate-check-sound
     (f/forall (conj bs ['accepted (eq-true (apply app (f/const* 'lp/certificate-check [U]) args))])
               (conclusion U 'I 'J 'matrix 'bounds 'costs 'plan 'row-list 'col-list))}))

(deftest frozen-statements-are-exact-native-and-axiom-free
  (let [ids (merge (reflection/definition-ids @checked) (reflection/theorem-ids @checked))]
    (is (= (set (keys frozen-types)) (set (keys ids))))
    (doseq [[alias expected] frozen-types]
      (let [declaration (environment/declaration @checked (get ids alias))]
        (testing (str alias)
          (is (= ['u] (:rainbow/universes declaration)))
          (is (= (if (#{'lp/all-at-most-decide 'lp/certificate-check} alias) :definition :theorem)
                 (:rainbow/kind declaration)))
          (is (= (core expected) (:rainbow/type declaration)))
          (is (= :native (get-in declaration [:rainbow/provenance :origin])))
          (is (= #{} (kernel/axioms @checked alias)))
          (is (= :checked (:status (kernel/check @checked (:rainbow/value declaration)
                                                 (:rainbow/type declaration) #{'u})))))))))

;; Independent literal data encoder for these tests, with no Pro generator import.
(defn- rational [v]
  (let [n (if (ratio? v) (numerator v) v)
        d (if (ratio? v) (denominator v) 1)
        nn #(app (c 'nnrat/make) [:nat %] [:nat (dec d)])]
    (app (c 'signed/make) (nn (max n 0)) (nn (max (- n) 0)))))
(defn- lookup [T values]
  (letfn [(at [values index]
            (if (= 1 (count values)) (first values)
                (app (f/const* 'data/Nat.rec [L])
                     (f/lam [['ignored N]] T) (first values)
                     (f/lam [['predecessor N] ['ignored T]] (at (subvec values 1) 'predecessor))
                     index)))]
    (f/lam [['lookup-index N]] (at (vec values) 'lookup-index))))
(defn- indices [xs]
  (reduce (fn [tail x] (app (f/const* 'data/cons [L]) N [:nat x] tail))
          (app (f/const* 'data/nil [L]) N) (reverse xs)))
(defn- args [{:keys [matrix capacities margins plan prices]}]
  (let [vector-of #(lookup Q (mapv rational %))]
    [N N (lookup (f/arrow N Q) (mapv vector-of matrix))
     (vector-of capacities) (vector-of margins) (vector-of plan) (vector-of prices)
     (indices (range (count capacities))) (indices (range (count margins)))]))
(defn- check-term [args] (apply app (f/const* 'lp/certificate-check [[:zero]]) args))
(defn- proof-term [args]
  (apply app (f/const* 'lp/certificate-check-sound [[:zero]])
         (conj args (app (f/const* 'equality/reflexive [L]) Bool (c 'data/true)))))
(defn- goal [[I J M b costs plan _ rows cols]]
  (conclusion [:zero] I J M b costs plan rows cols))
(defn- node-count [term]
  (count (filter #(and (vector? %) (#{:app :const :bound :lam :pi :let :nat :sort} (first %)))
                 (tree-seq vector? seq term))))

(deftest list-decision-checks-exactly-the-listed-indices
  (let [lower (lookup Q (mapv rational [0 3 0]))
        upper (lookup Q (mapv rational [1 2 0]))]
    (doseq [[xs expected] [[[] true] [[0 2 0] true] [[0 1] false] [[1 0] false]]]
      (let [ys (indices xs)
            decision (app (f/const* 'lp/all-at-most-decide [[:zero]]) N lower upper ys)
            witness (app (f/const* 'equality/reflexive [L]) Bool (c 'data/true))
            proof (app (f/const* 'lp/all-at-most-decide-sound [[:zero]]) N lower upper ys witness)]
        (is (= (normal (c (if expected 'data/true 'data/false))) (normal decision)))
        (is (= (if expected :checked :rejected)
               (:status (kernel/check @checked (core proof) (core (all-le [:zero] N lower upper ys))))))))))

(deftest every-certificate-clause-is-enforced
  (doseq [[label M b c0 x y expected]
          [[:valid 1 1 1 1 1 true]
           [:primal-only 1 0 0 1 0 false]
           [:dual-only 0 0 1 0 0 false]
           [:plan-sign-only 0 0 0 -1 0 false]
           [:price-sign-only 0 0 0 0 -1 false]
           [:gap-only 1 1 1 0 1 false]
           [:signed-coefficients -1 -1 -1 1 1 true]
           [:fractional 1/2 1/2 3/2 1 3 true]]]
    (testing (str label)
      (let [a (args {:matrix [[M]] :capacities [b] :margins [c0] :plan [x] :prices [y]})]
        (is (= (normal (c (if expected 'data/true 'data/false))) (normal (check-term a))))
        (is (= (if expected :checked :rejected)
               (:status (kernel/check @checked (core (proof-term a)) (core (goal a))))))))))

;; Minimization is encoded as maximizing the negated cost, exactly as in the bundle.
(def ^:private c2
  {:matrix [[1 1 1 0 0 0] [0 0 0 1 1 1] [-1 0 0 -1 0 0]
            [0 -1 0 0 -1 0] [0 0 -1 0 0 -1]]
   :capacities [18 8 -15 -2 -1] :margins [-8 -19 -33 0 -28 -26]
   :plan [7 2 1 8 0 0] :prices [0 8 8 19 33]})
(def ^:private fixture
  (delay
    (with-open [in (java.util.zip.GZIPInputStream.
                    (io/input-stream (io/resource "rainbow/fixtures/lp_c2_claim_types.edn.gz")))]
      (edn/read-string (slurp in)))))

(deftest c2-keeps-the-bundle-claim-type-and-rejects-a-changed-price
  (let [a (args c2)
        type (core (goal a))
        proof (core (proof-term a))
        original-type (get-in @fixture [:unary :type])
        literal-type (get-in @fixture [:literal :type])
        start (System/nanoTime)
        result (kernel/check @checked proof literal-type)
        elapsed (/ (- (System/nanoTime) start) 1e6)
        changed (args (update-in c2 [:prices 1] inc))
        rejected (kernel/check @checked (core (proof-term changed)) type)
        installed (support/add-spec @checked :signed-lp-certificate-reflect-test
                    {:name 'lp-reflection-test/c2 :universes []
                     :type (goal a) :value (proof-term a)})]
    (is (= type literal-type) "Exact core type of the preserved literal bundle")
    (is (true? (kernel/definitionally-equal? @checked type original-type))
        "Same mathematical statement as the original unary bundle")
    (is (= :checked (:status result)) (pr-str (dissoc result :term)))
    (is (= :checked (:status (kernel/check @checked proof original-type))))
    (is (= (normal (c 'data/true)) (normal (check-term a))))
    (is (= (normal (c 'data/false)) (normal (check-term changed))))
    (is (= :rejected (:status rejected)))
    (is (= :kernel/type-mismatch (get-in rejected [:error :error/category])))
    (is (= #{} (kernel/axioms installed 'lp-reflection-test/c2)))
    (is (< (node-count proof) (get-in @fixture [:literal :proof-nodes])))
    (println :C2 :proof-nodes (node-count proof) :type-nodes (node-count type)
             :proof-edn-bytes (alength (.getBytes (pr-str proof) "UTF-8"))
             :kernel-ms elapsed :status (:status result))
    (flush)))
