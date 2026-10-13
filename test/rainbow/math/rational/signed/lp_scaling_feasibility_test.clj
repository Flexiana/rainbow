(ns rainbow.math.rational.signed.lp-scaling-feasibility-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.lp-duality-on :as duality]
            [rainbow.math.rational.signed.lp-scaling-feasibility :as scaling]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def ^:private tl [:succ [:zero]])
(def ^:private N (f/const* 'data/Nat []))
(def ^:private S scaling/signed)
(def ^:private nz (f/const* 'data/zero []))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) nz) n))
(defn- rat [n] (app 'nnrat/make (numeral n) nz))
(defn- signed [n] (app 'signed/make (rat (max n 0)) (rat (max (- n) 0))))
(defn- constant [n] (f/lam [['i N]] (signed n)))
(defn- scale [d x] (app 'signed/scale d x))
(defn- scaled [d x] (f/lam [['i N]] (scale d (f/app x 'i))))
(defn- le [x y] (app 'signed/at-most x y))
(defn- all-le [x y idx] (poly 'signed/all-at-most N x y idx))
(defn- idx [n]
  (nth (iterate #(f/app (f/const* 'data/cons [tl]) N nz %)
                (f/app (f/const* 'data/nil [tl]) N)) n))
(defn- dot [left right indices]
  (poly 'signed/map-sum N
        (f/lam [['j N]] (app 'signed/multiply (f/app left 'j) (f/app right 'j)))
        indices))
(defn- activity [M x cols]
  (f/lam [['i N]] (dot (f/app M 'i) x cols)))
(defn- decided [left right]
  (app 'signed/decide-at-most-true-sound left right
       (f/app (f/const* 'equality/reflexive [tl])
              (f/const* 'data/Bool []) (f/const* 'data/true []))))
(defn- all-proof [left right count-of]
  (if (zero? count-of)
    (poly 'signed/all-at-most-empty N left right)
    (poly 'signed/all-at-most-cons N left right nz (idx (dec count-of))
          (decided (f/app left nz) (f/app right nz))
          (all-proof left right (dec count-of)))))

;; A genuine scaled universal certificate for max x subject to 0<=x<=2.
;; D=2 gives M'=2, b'=8, c'=4, y'=2. The variable remains arbitrary.
(def ^:private d (rat 2))
(def ^:private dd (app 'nnrat/multiply d d))
(def ^:private M (f/lam [['i N] ['j N]] (signed 1)))
(def ^:private b (constant 2))
(def ^:private c (constant 1))
(def ^:private y (constant 1))
(def ^:private sM (f/lam [['i N] ['j N]] (scale d (signed 1))))
(def ^:private sb (scaled dd b))
(def ^:private sc (scaled dd c))
(def ^:private sy (scaled d y))
(def ^:private zero-on (constant 0))
(defn- universal-type [matrix rhs margins prices]
  (f/forall
   [['candidate (f/arrow N S)]
    ['feasible (all-le (activity matrix 'candidate (idx 1)) rhs (idx 1))]
    ['nonnegative (all-le zero-on 'candidate (idx 1))]]
   (le (dot margins 'candidate (idx 1)) (dot rhs prices (idx 1)))))
(def ^:private scaled-universal-spec
  (let [type (universal-type sM sb sc sy)
        dual-price (f/lam [['j N]]
                         (poly 'signed/map-sum N
                               (f/lam [['i N]]
                                      (app 'signed/multiply
                                           (f/app (f/app sM 'i) 'j) (f/app sy 'i)))
                               (idx 1)))]
    {:name 'audit/lp-scaled-box-universal :universes [] :type type
     :value
     (f/lam (second type)
            (poly 'optimization/signed-lp-weak-duality-on N N sM sb sc
                  'candidate sy (idx 1) (idx 1)
                  'feasible (all-proof sc dual-price 1) 'nonnegative
                  (all-proof zero-on sy 1)))}))
(defn- transported [margins]
  (poly 'signed/lp-scaled-universal-bound-to-original
        N (numeral 1) nz M b margins y (idx 1) (idx 1)
        (f/const* 'audit/lp-scaled-box-universal [])))
(def ^:private original-universal-spec
  {:name 'audit/lp-original-box-universal :universes []
   :type (universal-type M b c y)
   :value (transported c)})

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (-> (:environment checkpoint) scaling/extend-environment duality/extend-environment
          decide/extend-environment
          (support/extend-with ::universal-example
                               [scaled-universal-spec original-universal-spec])))))
(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "Feasibility control did not elaborate" {:result r})))
    (:term r)))
(defn- check [env value type universes]
  (kernel/check env (elaborate! env value) (elaborate! env type) universes))

(deftest feasibility-and-universal-transport-are-axiom-free
  (let [env @checked-environment]
    (is (= #{'signed/scaling-preserves-nonnegative-on
             'signed/lp-scaling-preserves-primal-feasibility
             'signed/lp-scaled-universal-bound-to-original}
           (set (keys (scaling/theorem-ids env)))))
    (doseq [spec (concat scaling/theorem-specs [scaled-universal-spec original-universal-spec])]
      (let [id (environment/resolve-id env (:name spec))
            decl (environment/declaration env id)]
        (is (some? id))
        (is (= :checked (:status (kernel/check env (:rainbow/value decl) (:rainbow/type decl)
                                              (set (:rainbow/universes decl))))))
        (is (= #{} (kernel/axioms env id)))))))

(deftest untransported-premises-and-altered-margin-are-rejected
  (let [env @checked-environment]
    (doseq [[spec hypothesis]
            [[scaling/scaling-preserves-nonnegative-on-spec 'nonnegative]
             [scaling/lp-scaling-preserves-primal-feasibility-spec 'feasible]
             [scaling/lp-scaled-universal-bound-to-original-spec 'scaled-universal]]]
      (is (= :rejected (:status (check env (assoc (:value spec) 2 hypothesis)
                                      (:type spec) (set (:universes spec)))))))
    ;; Reuse of the max-x certificate cannot prove max-2x <= 2 for 0<=x<=2.
    (is (= :rejected (:status (check env (transported (constant 2))
                                    (universal-type M b (constant 2) y) #{}))))))

(deftest listed-constraints-empty-and-invalid-source-controls
  (let [env @checked-environment]
    (doseq [[value capacity rows cols valid?]
            [[1 3 2 2 true] [1 0 1 0 true] [2 1 0 1 true] [2 1 1 1 false]]]
      (let [x (constant value) rhs (constant capacity)
            source (activity M x (idx cols))
            target (activity sM (scaled d x) (idx cols))
            proof (poly 'signed/lp-scaling-preserves-primal-feasibility
                        N N d M rhs x (idx rows) (idx cols)
                        (all-proof source rhs rows))]
        (is (= (if valid? :checked :rejected)
               (:status (check env proof (all-le target (scaled dd rhs) (idx rows)) #{})))
            (str "Feasibility control " [value capacity rows cols]))))))

(deftest nonnegativity-does-not-accept-a-false-source-premise
  (let [env @checked-environment]
    (doseq [[rate value count-of valid?] [[2 1 2 true] [2 -1 1 false]
                                        [2 -1 0 true] [0 -1 1 false]]]
      (let [factor (rat rate) x (constant value)
            proof (poly 'signed/scaling-preserves-nonnegative-on
                        N factor x (idx count-of) (all-proof zero-on x count-of))]
        (is (= (if valid? :checked :rejected)
               (:status (check env proof
                               (all-le zero-on (scaled factor x) (idx count-of)) #{})))
            (str "Nonnegativity control " [rate value count-of]))))))
