(ns rainbow.math.rational.nnrat.farkas-cross-bridge-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-cross-bridge :as bridge]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (bridge/extend-environment (:environment checkpoint)))))

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

(deftest cross-condition-with-affine-blocks-is-a-both-sides-row
  (testing "piece 1 core of the n-variable capstone: a cross condition whose
            survivor blocks are affine in the next variable w (s = c*w + d)
            IS the both-sides row A*w+P <= B*w+Q with A=c_hi*a_lo etc. --
            realigned by distribute-right + multiply-swap-right +
            add-swap-right, transported by at-most-respects. Discharges the
            eliminate-round's structural `link`. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (bridge/definition-ids env) (bridge/theorem-ids env))]
      (is (= #{'nnrat/farkas-cross-to-both-sides}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest cross-bridge-retains-equivalence-transport
  (testing "the affine bridge remains an at-most equivalence transport, not
            an unrelated proof of the target inequality"
    (is (pos? (body-symbol-count (:value bridge/cross-to-both-sides-spec)
                                 'nnrat/at-most-respects-equivalence)))) )
