(ns rainbow.math.rational.nnrat.farkas-additive-cross-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-additive-cross :as cross]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (cross/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- contains-symbol? [form symbol]
  "Structural anti-vacuity guard for the two premise arguments.

  Kernel checking proves that the term inhabits its declared type, but a
  future refactor could accidentally stop mentioning a premise if the
  conclusion became independently provable.  This guard is deliberately
  syntactic and supplementary: it does not replace kernel checking or claim
  semantic independence testing."
  (boolean
   (some #(= symbol %)
         (tree-seq coll? seq form))))

(defn- body-symbol-count [form symbol]
  "Count occurrences outside `:fn` binder vectors in a source proof term."
  (cond
    (and (vector? form) (= :fn (first form)))
    (body-symbol-count (nth form 2) symbol)

    (coll? form)
    (reduce + (map #(body-symbol-count % symbol) form))

    (= symbol form) 1
    :else 0))

(deftest additive-cross-necessary-holds
  (testing "brick 5c core of the general LP FM encoding: the additive
            cross-elimination crux -- from w <= v + s_lo and v + s_hi <= b,
            eliminating v yields w + s_hi <= b + s_lo (necessary/certificate
            direction), by reassociation up to nnrat equivalence and
            transitivity. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (cross/definition-ids env) (cross/theorem-ids env))]
      (is (= #{'nnrat/farkas-additive-cross-necessary}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name)))
      ;; Inspect the source spec as well as the registered declaration.  The
      ;; environment stores canonicalized proof data, so the original binder
      ;; names are available only at this construction boundary.
      (let [spec cross/additive-cross-necessary-spec
            value (:value spec)
            type (:type spec)]
        (testing "both elimination premises remain load-bearing in the term"
          (is (contains-symbol? type 'lower))
          (is (contains-symbol? type 'upper))
          (is (contains-symbol? value 'lower))
          (is (contains-symbol? value 'upper))
          (is (pos? (body-symbol-count value 'lower)))
          (is (pos? (body-symbol-count value 'upper))))))))
