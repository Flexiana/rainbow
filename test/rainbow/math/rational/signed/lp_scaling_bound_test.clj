(ns rainbow.math.rational.signed.lp-scaling-bound-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.lp-scaling-bound :as bounds]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (-> (:environment checkpoint) bounds/extend-environment decide/extend-environment))))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def ^:private tl [:succ [:zero]])
(def ^:private N (f/const* 'data/Nat []))
(def ^:private nz (f/const* 'data/zero []))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) nz) n))
(defn- rat [n] (app 'nnrat/make (numeral n) nz))
(defn- signed [n] (app 'signed/make (rat (max n 0)) (rat (max (- n) 0))))
(defn- indices [n]
  (nth (iterate #(f/app (f/const* 'data/cons [tl]) N nz %)
                (f/app (f/const* 'data/nil [tl]) N)) n))
(defn- constant [n] (f/lam [['i N]] (signed n)))
(defn- le [x y] (app 'signed/at-most x y))
(defn- scaled-objective [d c x idx]
  (poly 'signed/map-sum N
        (f/lam [['i N]]
               (app 'signed/multiply
                    (app 'signed/scale (app 'nnrat/multiply d d) (f/app c 'i))
                    (app 'signed/scale d (f/app x 'i)))) idx))
(defn- decide-proof [left right]
  (app 'signed/decide-at-most-true-sound left right
       (f/app (f/const* 'equality/reflexive [tl])
              (f/const* 'data/Bool []) (f/const* 'data/true []))))
(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "LP scaling control did not elaborate" {:result r})))
    (:term r)))
(defn- check [env value type universes]
  (kernel/check env (elaborate! env value) (elaborate! env type) universes))

(deftest cubic-reflection-and-objective-bound-are-axiom-free
  (let [env @checked-environment
        ids (bounds/theorem-ids env)]
    (is (= #{'signed/scale-positive-cube-reflects-order
             'signed/lp-scaled-objectives-bound} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                              (set (:rainbow/universes d))))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest unchanged-scaled-premise-does-not-prove-original-bound
  (let [env @checked-environment]
    (doseq [[spec hypothesis] [[bounds/scale-positive-cube-reflects-order-spec 'ordered]
                              [bounds/lp-scaled-objectives-bound-spec 'scaled-bound]]]
      (is (= :rejected
             (:status (check env (assoc (:value spec) 2 hypothesis) (:type spec)
                             (set (:universes spec)))))))))

(deftest concrete-loose-negative-empty-and-false-bounds
  (let [env @checked-environment]
    (doseq [[margin capacity ncols nrows left right valid?]
            [[2 3 1 1 2 3 true]
             [-2 -3 2 1 -4 -3 true]
             [7 3 0 1 0 3 true]
             [2 1 1 1 2 1 false]]]
      (let [d (rat 2) c (constant margin) b (constant capacity) x (constant 1)
            cols (indices ncols) rows (indices nrows)
            scaled-left (scaled-objective d c x cols)
            scaled-right (scaled-objective d b x rows)
            premise (decide-proof scaled-left scaled-right)
            forged (app 'signed/at-most-reflexive scaled-right)
            instantiate (fn [h]
                          (poly 'signed/lp-scaled-objectives-bound
                                N (numeral 1) nz c x b x cols rows h))
            target (le (signed left) (signed right))]
        (is (= (if valid? :checked :rejected)
               (:status (check env (instantiate premise) target #{})))
            (str "Original objective bound " left " <= " right))
        ;; Each pair is deliberately non-tight, so right<=right cannot be
        ;; substituted for the scaled-left<=scaled-right hypothesis.
        (is (= :rejected (:status (check env (instantiate forged) target #{})))
            "An unrelated reflexive bound must not satisfy the premise")))))
