(ns rainbow.math.finite.signed-argmax-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.signed-argmax :as argmax]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (argmax/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-signed-argmax-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (argmax/definition-ids env)
        theorems (argmax/theorem-ids env)]
    (is (= #{'decision/signed-select
             'list/signed-argmax-from
             'decision/finite-signed-argmax}
           (set (keys definitions))))
    (is (= #{'decision/signed-select-is-left-or-right
             'decision/signed-select-left-bound
             'decision/signed-select-right-bound
             'list/signed-argmax-from-bounds-initial
             'list/signed-argmax-from-bounds-member
             'list/signed-argmax-from-is-initial-or-member
             'decision/finite-signed-argmax-is-member
             'decision/finite-signed-argmax-dominates}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
