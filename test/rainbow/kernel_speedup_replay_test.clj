(ns rainbow.kernel-speedup-replay-test
  "Replay an existing saved environment independently through both kernels."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as env]
            [rainbow.kernel :as kernel]
            [rainbow.kernel-speedup-reference.kernel :as old]
            [rainbow.persistence :as persistence]))

(deftest saved-checkpoint-has-the-same-declaration-verdicts-and-identities
  (let [loaded (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")
        _ (is (= :replayed (:status loaded)))
        artifact (persistence/environment-artifact (:environment loaded))
        final
        (binding [kernel/*reduction-budget* 10000000 old/*reduction-budget* 10000000]
          (reduce
           (fn [[before after] {:entry/keys [kind value]}]
             (let [a ((if (= kind :inductive-block) old/add-inductive-block old/add-declaration) before value)
                   b ((if (= kind :inductive-block) kernel/add-inductive-block kernel/add-declaration) after value)]
               (is (= :accepted (:status a) (:status b)) (str kind " " (:rainbow/id value)))
               (when-not (= :accepted (:status a) (:status b))
                 (throw (ex-info "Differential replay failed" {:id (:rainbow/id value) :before (dissoc a :environment) :after (dissoc b :environment)})))
               [(:environment a) (:environment b)]))
           [(env/empty-environment) (env/empty-environment)]
           (:rainbow.artifact/entries artifact)))]
    (is (= (:rainbow.artifact/environment-id artifact)
           (env/environment-id (first final)) (env/environment-id (second final))))
    (println "DIFFERENTIAL-REPLAY" (count (:rainbow.environment/declarations (first final)))
             (env/environment-id (first final)))))
