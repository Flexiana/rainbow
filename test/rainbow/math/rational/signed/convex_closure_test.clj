(ns rainbow.math.rational.signed.convex-closure-test
  "Gate for convexity closure: sum of convex functions is convex, and nonnegative
  scaling preserves convexity, both kernel-checked and axiom-free. Discrimination
  control: dropping the 0<=c hypothesis from convex-nonneg-scale makes the statement
  false (negative c flips convexity), and the kernel rejects the value against that
  weakened type -- the nonnegativity premise is load-bearing."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.convex-closure :as closure]))

(def ^:private signed (f/const* 'signed/SignedRational []))
(def ^:private sig-fn (f/arrow signed signed))
(defn- app [nm & a] (apply f/app (f/const* nm []) a))
(defn- convex-on [g] (app 'signed/convex-on g))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (closure/extend-environment (:environment checkpoint)))))

(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "expression failed elaboration" {:result r})))
    (:term r)))
(defn- check [env value type universes]
  (kernel/check env (elaborate! env value) (elaborate! env type) universes))

(deftest convex-closure-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (closure/theorem-ids env)]
    (is (= #{'signed/convex-sum 'signed/convex-nonneg-scale 'signed/convex-max}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest nonnegativity-hypothesis-is-load-bearing
  (let [env @checked-environment
        spec closure/convex-nonneg-scale-spec
        ;; Drop the 0<=c premise: without it the statement is false for c<0.
        wrong-type (f/forall
                    [['c signed] ['f sig-fn] ['cf (convex-on 'f)]]
                    (convex-on (f/lam [['x signed]] (app 'signed/multiply 'c (f/app 'f 'x)))))]
    (is (not= (:type spec) wrong-type))
    (is (= :rejected (:status (check env (:value spec) wrong-type #{}))))))
