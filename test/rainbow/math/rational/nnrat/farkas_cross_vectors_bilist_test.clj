(ns rainbow.math.rational.nnrat.farkas-cross-vectors-bilist-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-cross-vectors-bilist :as cvb]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (cvb/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- body-symbol-count [form symbol]
  (cond
    (and (vector? form) (= :fn (first form)))
    (body-symbol-count (nth form 2) symbol)
    (coll? form)
    (reduce + (map #(body-symbol-count % symbol) form))
    (= symbol form) 1
    :else 0))

(deftest one-full-round-on-coefficient-vector-constraints
  (testing "brick 3 full round: a LIST of lower and a LIST of upper
            coefficient-vector constraints, all holding at x1, produce every
            pairwise reduced both-sides vector constraint -- the per-pair
            fold mapped over the lower list by a second List.rec. One full
            elimination round on the coefficient-vector representation.
            Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (cvb/definition-ids env) (cvb/theorem-ids env))]
      (is (= #{'nnrat/farkas-cross-vectors-lowers-hold
               'nnrat/farkas-cross-vectors-all-reduced-conds
               'nnrat/farkas-cross-vectors-all-reduced}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest all-reduced-body-retains-nested-fold
  (testing "the all-reduced theorem remains a lower-list recursion whose
            cons case invokes the per-lower reduced fold"
    (doseq [symbol ['data/List.rec
                    'nnrat/farkas-cross-vectors-reduced-holds]]
      (is (pos? (body-symbol-count (:value cvb/all-reduced-necessary-spec) symbol))
          (str (:name cvb/all-reduced-necessary-spec) " body depends on " symbol)))))
