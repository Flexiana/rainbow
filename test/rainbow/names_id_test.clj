(ns rainbow.names-id-test
  "Claim integrity A1: the environment id covers declarations only, so a checkpoint whose aliases
  were swapped (and whose checkpoint id was recomputed) replays to the same environment id, and a
  claim read by name then means something else. The names id covers the alias bindings."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.canonical :as canonical]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def path "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")

(defn- swap-aliases [declaration a b]
  (update declaration :rainbow/aliases
          (fn [aliases] (set (map #(condp = % a b b a %) aliases)))))

(deftest swapped-aliases-keep-the-environment-id-and-change-the-names-id
  (let [original (#'checkpoint/read-value path)   ; the checkpoint reader: published trees store checkpoints packed
        swap #(swap-aliases % 'algebra/nat-add 'nat/multiply)
        tampered (-> original
                     (update-in [:environment :rainbow.artifact/declarations] (partial mapv swap))
                     (update-in [:environment :rainbow.artifact/entries]
                                (partial mapv #(cond-> % (= :declaration (:entry/kind %)) (update :entry/value swap))))
                     (dissoc :rainbow.checkpoint/id))
        tampered (assoc tampered :rainbow.checkpoint/id (canonical/content-id tampered))
        honest (checkpoint/replay-checkpoint original)
        forged (checkpoint/replay-checkpoint tampered)]
    (is (= :replayed (:status honest) (:status forged)) "the tampered checkpoint still replays")
    (is (not= (environment/resolve-id (:environment honest) 'algebra/nat-add)
              (environment/resolve-id (:environment forged) 'algebra/nat-add))
        "the name now points at another declaration")
    (is (= (:environment/id honest) (:environment/id forged)) "the environment id cannot see it")
    (let [two-plus-three (fn [env] [:app [:app [:const (environment/resolve-id env 'algebra/nat-add) []] [:nat 2]] [:nat 3]])
          ;; kernel/normalize returns unary numerals: count the data/succ applications
          value (fn [env] (:term (kernel/normalize env (two-plus-three env) {})))]
      (is (= 5 (count (filter #{[:const (environment/resolve-id (:environment honest) 'data/succ) []]}
                              (tree-seq vector? seq (value (:environment honest)))))))
      (is (= 6 (count (filter #{[:const (environment/resolve-id (:environment honest) 'data/succ) []]}
                              (tree-seq vector? seq (value (:environment forged))))))
          "by name, 2 + 3 is now 6"))
    (is (string? (:names/id honest)))
    (is (not= (:names/id honest) (:names/id forged)) "the names id can")))
