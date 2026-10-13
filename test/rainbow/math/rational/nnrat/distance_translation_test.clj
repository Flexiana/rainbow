(ns rainbow.math.rational.nnrat.distance-translation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.nnrat.distance-translation :as translation]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (translation/extend-environment (:environment checkpoint)))))

(deftest common-mass-cancels-from-distance
  (let [env @checked-environment
        id (get (translation/theorem-ids env) 'nnrat/distance-add-right)
        d (environment/declaration env id)]
    (is (some? id))
    (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{}))))
    (is (= #{} (kernel/axioms env id)))))

(defn- c [name] (f/const* name []))
(defn- numeral [n]
  (nth (iterate #(f/app (c 'data/succ) %) (c 'data/zero)) n))
(defn- rational [n d]
  (f/app (c 'nnrat/make) (numeral n) (numeral (dec d))))
(defn- check-instance [a b common right-common]
  (let [env @checked-environment
        proof (f/app (c 'nnrat/distance-add-right) a b common)
        type (f/app (c 'nnrat/equivalent)
                    (f/app (c 'nnrat/distance)
                           (f/app (c 'nnrat/add) a common)
                           (f/app (c 'nnrat/add) b right-common))
                    (f/app (c 'nnrat/distance) a b))
        core (fn [surface]
               (let [r (elaborate/core-expression env surface)]
                 (when-not (= :elaborated (:status r))
                   (throw (ex-info "Instance failed elaboration" r)))
                 (:term r)))]
    (kernel/check env (core proof) (core type) #{})))

(deftest translation-handles-zero-and-noncanonical-representations
  (doseq [[a b common] [[(rational 0 1) (rational 0 3) (rational 2 1)]
                         [(rational 1 2) (rational 2 4) (rational 1 3)]
                         [(rational 7 3) (rational 1 2) (rational 2 1)]]]
    (let [result (check-instance a b common common)]
      (is (= :checked (:status result)) (str result))))
  ;; Different additions do not cancel: |(0+1)-(0+0)| is not |0-0|.
  (let [result (check-instance (rational 0 1) (rational 0 1)
                               (rational 1 1) (rational 0 1))]
    (is (= :rejected (:status result)))
    (is (= :kernel/type-mismatch (get-in result [:error :error/category])))))
