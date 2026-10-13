(ns rainbow.algorithms.proofs.ahof.linear-interpolation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.linear-interpolation :as lerp]
            [rainbow.algorithms.proofs.ahof.o72-branch-and-bound :as o72]
            [rainbow.algorithms.proofs.branch-and-bound :as bnb]))

(def base
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (:environment c))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest linear-interpolation-is-native-axiom-free
  (let [env (lerp/extend-environment @base)
        ids (merge (lerp/definition-ids env) (lerp/theorem-ids env))]
    (is (contains? (set (keys ids)) 'interp/linear-interpolation))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))

(deftest o72-branch-and-bound-reuse-is-native-axiom-free
  (let [env (-> @base bnb/extend-environment o72/extend-environment)
        ids (merge (o72/definition-ids env) (o72/theorem-ids env))]
    (is (= #{'ahof-o72/prunes-weak-node 'ahof-o72/pruning-sound
             'ahof-o72/explores-strong-node 'ahof-o72/branch-and-bound}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
