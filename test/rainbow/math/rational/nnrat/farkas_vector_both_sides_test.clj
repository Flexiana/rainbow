(ns rainbow.math.rational.nnrat.farkas-vector-both-sides-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-both-sides :as vbs]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vbs/extend-environment (:environment checkpoint)))))

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

(deftest reduced-vector-row-becomes-a-lower-or-upper-row-in-the-next-variable
  (testing "the coefficient-vector partition's per-row core: a reduced
            both-sides vector row whose tails are headed by the next variable
            x2 is affine in x2 on both sides, so with the difference witness it
            converts (subtraction-free) to a lower row (to-lower, x2 bounded
            below) or an upper row (to-upper, x2 bounded above) -- the rows the
            next elimination round crosses. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (vbs/definition-ids env) (vbs/theorem-ids env))]
      (is (= #{'nnrat/farkas-vector-both-sides-to-lower
               'nnrat/farkas-vector-both-sides-to-upper}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest projection-bodies-retain-directional-cores
  (testing "lower and upper projections remain applications of their
            directional generic cores"
    (is (pos? (body-symbol-count (:value vbs/vector-both-sides-to-lower-spec)
                                 'nnrat/farkas-both-sides-to-lower)))
    (is (pos? (body-symbol-count (:value vbs/vector-both-sides-to-upper-spec)
                                 'nnrat/farkas-both-sides-to-upper)))) )
