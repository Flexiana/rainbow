(ns rainbow.math.rational.nnrat.commutative-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.commutative :as commutative]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d61-q-learning/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D61 checkpoint rejected" {:checkpoint checkpoint})))
      (commutative/extend-environment (:environment checkpoint)))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest rational-commutativity-laws-are-native-general-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (commutative/theorem-ids checked-environment)]
    (is (= #{'nnrat/add-commutative 'nnrat/multiply-commutative
             'signed/add-commutative}
           (set (keys theorems))))
    ;; General laws over arbitrary rationals, axiom-free -- not worked instances.
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest commutativity-instantiates-at-concrete-rationals
  ;; The general law applies to specific rationals: (1/2 + 1/1) ~ (1/1 + 1/2).
  (let [env @checked-environment
        half [:const 'nnrat/half []]
        one [:const 'nnrat/one []]
        add-comm [:const 'nnrat/add-commutative []]
        goal [:app [:const 'nnrat/equivalent []]
              [:app [:const 'nnrat/add []] half one]
              [:app [:const 'nnrat/add []] one half]]
        proof [:app add-comm half one]
        elaborated-goal (:term (elaborate/core-expression env goal))
        elaborated-proof (:term (elaborate/core-expression env proof))]
    (is (= :checked (:status (kernel/check env elaborated-proof
                                           elaborated-goal #{}))))))
