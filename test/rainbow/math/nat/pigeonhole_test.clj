(ns rainbow.math.nat.pigeonhole-test
  "Cold gate: the constructive pigeonhole principle on Nat (nat/pigeonhole) with trichotomy and
  bounded search, kernel-checked and axiom-free. On data: every map from 0..n into 0..n-1 repeats,
  checked exhaustively for n <= 4. DISCRIMINATION: with the codomain one larger (values below
  n + 1), the identity on 0..n does NOT repeat, so the bound in the hypothesis is doing the work."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.pigeonhole :as m]))

(def checked-environment
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "checkpoint" {})))
           (-> (:environment cp) m/extend-environment))))

(deftest pigeonhole-checked-axiom-free
  (let [env @checked-environment ids (m/theorem-ids env)]
    (is (= 3 (count ids)))
    (doseq [[nm id] ids]
      (is (some? id) (str nm " installed"))
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                               (set (:rainbow/universes d))))) (str nm))
        (is (= #{} (kernel/axioms env id)) (str nm))))))

(defn- maps [dom cod] (if (zero? dom) [[]] (for [m (maps (dec dom) cod) v (range cod)] (conj m v))))
(defn- repeats? [f] (some (fn [[a b]] (= (f a) (f b))) (for [b (range (count f)) a (range b)] [a b])))

(deftest n-plus-one-values-below-n-repeat
  (testing "exhaustive: every f : 0..n -> 0..n-1 has a < b <= n with f a = f b"
    (doseq [n (range 1 5) f (maps (inc n) n)]
      (is (repeats? f) (str n " " f))))
  (testing "discrimination: values below n + 1 need not repeat (the identity on 0..n)"
    (doseq [n (range 1 6)]
      (is (not (repeats? (vec (range (inc n)))))))))
