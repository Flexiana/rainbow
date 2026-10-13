(ns rainbow.algorithms.proofs.ahof.game-equilibria-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.game-equilibria :as ge]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (ge/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest game-equilibria-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (ge/definition-ids env) (ge/theorem-ids env))]
    (is (= #{'game/maximin 'game/minimax 'game/pomg-value 'game/dec-ibr-value 'game/levelk-value
             'game/minimax-inequality 'game/pomg-no-deviation 'game/dec-ibr-no-deviation
             'game/levelk-no-deviation}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
