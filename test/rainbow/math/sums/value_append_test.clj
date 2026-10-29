(ns rainbow.math.sums.value-append-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s]
            [rainbow.math.sums.value-append :as m]
            [rainbow.or.lp-certificate :as literals]))

(def checked-environment
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "Checkpoint rejected" {})))
           (m/extend-environment (:environment cp)))))
(defn- core! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- check [label proof target expected]
  (let [env @checked-environment r (kernel/check env (core! env proof) (core! env target) #{})]
    (println :append-control label (:status r))
    (is (= expected (:status r)) (str label))
    (when (= expected :rejected)
      (is (= :kernel/type-mismatch (get-in r [:error :error/category])) (str label)))))
(defn- nn [n] (nth (iterate s/succ s/nz) n))
(defn- lit [x] (#'literals/signed-literal x))

(deftest declaration-is-checked-with-no-axioms
  (let [env @checked-environment ids (m/theorem-ids env)]
    (is (= 1 (count ids)))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)
            r (kernel/check env (:rainbow/value d) (:rainbow/type d) #{})
            axioms (kernel/axioms env id)]
        (println name (:status r) :axioms axioms)
        (is (= :checked (:status r)))
        (is (= #{} axioms))))))

(deftest nonconstant-signed-family-and-empty-parts
  (let [F (#'literals/nat-lookup s/signed (mapv lit [2 -1 4]))]
    (doseq [[a b] [[0 0] [0 3] [3 0] [1 2]]]
      (let [a (nn a) b (nn b) shift (f/lam [['i s/nat]] (s/at F (m/nadd 'i a)))
            proof (s/call 'signed/expr-sum-value-append F a b)]
        (check [a b] proof (s/eqv (s/sum F (m/nadd b a))
                                 (s/add (s/sum F a) (s/sum shift b))) :checked)))
    ;; With a=1,b=2 the true split is 2+(-1+4)=5. Omitting the
    ;; offset instead produces 2+(2-1)=3; this is a false equality.
    (let [a (nn 1) b (nn 2) proof (s/call 'signed/expr-sum-value-append F a b)]
      (check :missing-offset proof
             (s/eqv (s/sum F (m/nadd b a)) (s/add (s/sum F a) (s/sum F b))) :rejected))))

(deftest reflexivity-cannot-inhabit-the-universal-law
  (let [[_ bindings _] (:type m/append-spec)
        proof (f/lam bindings (s/refl (s/sum 'F (m/nadd 'b 'a))))]
    (check :reflexivity-passthrough proof (:type m/append-spec) :rejected)))
