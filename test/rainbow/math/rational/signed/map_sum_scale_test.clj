(ns rainbow.math.rational.signed.map-sum-scale-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.walk :as walk]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.map-sum-scale :as scaling]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (scaling/extend-environment (:environment checkpoint)))))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- at-zero [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def ^:private tl [:succ [:zero]])
(def ^:private nat (f/const* 'data/Nat []))
(def ^:private nz (f/const* 'data/zero []))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) nz) n))
(defn- rat [n] (app 'nnrat/make (numeral n) nz))
(defn- signed-literal [n]
  (app 'signed/make (rat (max 0 n)) (rat (max 0 (- n)))))
(def ^:private empty-indices (f/app (f/const* 'data/nil [tl]) nat))
(def ^:private repeated-indices
  (f/app (f/const* 'data/cons [tl]) nat nz
         (f/app (f/const* 'data/cons [tl]) nat nz empty-indices)))
(defn- constant-mapping [n] (f/lam [['i nat]] (signed-literal n)))
(defn- eqv [x y] (app 'signed/equivalent x y))
(defn- scale [c x] (app 'signed/scale c x))
(defn- scaled-objective [d coefficient value indices]
  (at-zero 'signed/map-sum nat
           (f/lam [['i nat]]
                  (app 'signed/multiply
                       (scale (ring/rmul d d) (f/app coefficient 'i))
                       (scale d (f/app value 'i))))
           indices))
(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "Objective-scaling expression failed elaboration" {:result r})))
    (:term r)))
(defn- check [env value type universes]
  (kernel/check env (elaborate! env value) (elaborate! env type) universes))

(deftest sum-and-objective-scaling-are-native-and-axiom-free
  (let [env @checked-environment
        ids (scaling/theorem-ids env)]
    (is (= #{'signed/map-sum-nnrat-scale 'signed/multiply-scaled-factors
             'signed/map-sum-biscaled-products 'signed/lp-objective-cubic-scale}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d))))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest cubic-factor-cannot-be-replaced-by-square
  (let [env @checked-environment
        spec scaling/lp-objective-cubic-scale-spec
        ;; Change only the conclusion's aggregate factor, not the actual D^2/D
        ;; scaling on the left. Failure must occur in the kernel, not setup.
        wrong-type (walk/postwalk-replace
                    {(ring/rmul (ring/rmul 'd 'd) 'd) (ring/rmul 'd 'd)}
                    (:type spec))]
    (is (not= (:type spec) wrong-type))
    (is (= :rejected (:status (check env (:value spec) wrong-type #{'u}))))))

(deftest concrete-signed-objectives-empty-and-repeated-indices
  (let [env @checked-environment]
    (doseq [[d coefficient value indices expected wrong]
            [[2 -2 1 repeated-indices -32 -16]
             [2 -2 -1 repeated-indices 32 16]
             [2 -2 1 empty-indices 0 -16]
             [0 -2 1 repeated-indices 0 -4]]]
      (let [rate (rat d)
            coefficients (constant-mapping coefficient)
            values (constant-mapping value)
            proof (at-zero 'signed/lp-objective-cubic-scale
                           nat rate coefficients values indices)
            lhs (scaled-objective rate coefficients values indices)]
        (is (= :checked (:status (check env proof (eqv lhs (signed-literal expected)) #{})))
            (str "Correct signed objective: " [d coefficient value expected]))
        (is (= :rejected (:status (check env proof (eqv lhs (signed-literal wrong)) #{})))
            (str "Wrong reported objective rejected: " wrong))))))
