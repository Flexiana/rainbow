(ns rainbow.math.rational.division-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.division :as division]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o32-coordinate-search/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O32 checkpoint rejected" {:checkpoint checkpoint})))
      (division/extend-environment (:environment checkpoint)))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest rational-division-is-native-and-axiom-free
  (let [checked-environment @checked-environment
        definitions (division/definition-ids checked-environment)
        theorems (division/theorem-ids checked-environment)]
    (is (= #{'nnrat/reciprocal 'nnrat/divide} (set (keys definitions))))
    (is (= #{'nnrat/reciprocal-unfold 'nnrat/divide-unfold
             'nnrat/divide-self-positive}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest divide-self-positive-instantiates-at-concrete-rationals
  ;; The general law applies to specific positive rationals: dividing 3/2 by
  ;; itself is equivalent to 1 (here 3/2 = make (succ 2) 1, so p=2, q=1).
  (let [env @checked-environment
        two [:const 'data/zero []]
        succ (fn [n] [:app [:const 'data/succ []] n])
        p (succ (succ two)) ; 2
        q (succ two)        ; 1
        three-halves [:app [:app [:const 'nnrat/make []] (succ p)] q]
        goal [:app [:app [:const 'nnrat/equivalent []]
                    [:app [:app [:const 'nnrat/divide []] three-halves]
                     three-halves]]
              [:const 'nnrat/one []]]
        proof [:app [:app [:const 'nnrat/divide-self-positive []] p] q]
        elaborated-goal (:term (elaborate/core-expression env goal))
        elaborated-proof (:term (elaborate/core-expression env proof))]
    (is (= :checked (:status (kernel/check env elaborated-proof
                                           elaborated-goal #{}))))))
