(ns rainbow.math.rational.signed.lp-free-price-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-free-price :as price]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (price/extend-environment (:environment r)))))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- lit [x] (#'lp/signed-literal x))
(defn- core! [expression]
  (let [r (elaborate/core-expression @env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- check [label value target]
  (let [r (kernel/check @env (core! value) (core! target) #{})
        result {:status (:status r) :category (get-in r [:error :error/category])}]
    (println "LP-FREE-PRICE" label (pr-str result))
    result))
(defn- target [v p pp pm]
  (app 'signed/equivalent (app 'signed/multiply v p)
       (app 'signed/add (app 'signed/multiply v pp)
            (app 'signed/multiply (app 'signed/negate v) pm))))

(deftest generic-declarations-check-and-have-empty-axiom-closures
  (doseq [[name id] (price/theorem-ids @env)]
    (let [d (environment/declaration @env id)
          r (kernel/check @env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d)))]
      (println "LP-FREE-PRICE-THEOREM" name id (:status r) (kernel/axioms @env id))
      (is (some? id))
      (is (= :checked (:status r)))
      (is (= #{} (kernel/axioms @env id))))))

(deftest certified-splits-and-forged-premises
  ;; The contribution law itself does not require nonnegative split components.
  ;; A zero coefficient must not hide a forged (false) split premise either.
  (doseq [[coefficient p pp pm valid?]
          [[2 3 3 0 true] [-2 -3 0 3 true] [3 0 0 0 true]
           [-2 2 5 3 true] [2 1/2 3/2 1 true] [1 1 -1 -2 true]
           [2 2 5 2 false] [0 2 5 2 false]]]
    (let [[v p pp pm] (mapv lit [coefficient p pp pm])
          split (app 'signed/subtract pp pm)
          proof (app 'signed/lp-free-price-split-contribution v p pp pm
                     (#'lp/computed-equivalence p split))
          r (check [coefficient valid?] proof (target v p pp pm))]
      (is (= (if valid? :checked :rejected) (:status r)))
      (when-not valid? (is (= :kernel/type-mismatch (:category r)))))))

(deftest noncanonical-witnesses-and-wrong-sign-control
  (doseq [[positive negative] [[3 0] [0 2] [0 0] [5 3] [3/2 1/2]]]
    (let [P (app 'signed/positive (lit positive))
          N (app 'signed/positive (lit negative))
          p (app 'signed/make P N)
          pp (app 'signed/from-nnrat P) pm (app 'signed/from-nnrat N)
          v (lit -2)
          result (check [:components positive negative]
                        (app 'signed/lp-price-components-contribution v p)
                        (target v p pp pm))
          nonnegative (app 'proposition/conjunction
                           (app 'signed/at-most price/zero pp)
                           (app 'signed/at-most price/zero pm))]
      (is (= :checked (:status result)))
      (is (= :checked (:status (check [:nonnegative positive negative]
                                     (app 'signed/lp-price-components-nonnegative p)
                                     nonnegative))))))
  (let [v (lit 2) p (lit -3)
        proof (app 'signed/lp-price-components-contribution v p)
        ;; Deliberately omit negation of the second row: -6 is not +6.
        wrong (app 'signed/equivalent (app 'signed/multiply v p)
                   (app 'signed/add (app 'signed/multiply v (lit 0))
                        (app 'signed/multiply v (lit 3))))
        r (check :wrong-second-row-sign proof wrong)]
    (is (= :rejected (:status r)))
    (is (= :kernel/type-mismatch (:category r)))))
