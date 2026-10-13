(ns rainbow.math.rational.signed.absolute-convex-test
  "Gate for absolute-value convexity: |x| is convex, kernel-checked and axiom-free.
  Discrimination control: the same proof does NOT inhabit the concave claim
  convex-on (x |-> -|x|), which is false -- the kernel rejects it."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.absolute-convex :as absconv]))

(def ^:private signed (f/const* 'signed/SignedRational []))
(defn- app [nm & a] (apply f/app (f/const* nm []) a))
(defn- convex-on [g] (app 'signed/convex-on g))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (absconv/extend-environment (:environment checkpoint)))))

(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "expression failed elaboration" {:result r})))
    (:term r)))
(defn- check [env value type universes]
  (kernel/check env (elaborate! env value) (elaborate! env type) universes))

(deftest absolute-convex-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (absconv/theorem-ids env)]
    (is (= #{'signed/absolute-convex} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest the-proof-does-not-inhabit-the-concave-claim
  (let [env @checked-environment
        spec absconv/absolute-convex-spec
        ;; -|x| is concave, not convex: the convexity inequality is false for it.
        wrong-type (convex-on (f/lam [['x signed]]
                                     (app 'signed/negate (app 'signed/absolute 'x))))]
    (is (not= (:type spec) wrong-type))
    (is (= :rejected (:status (check env (:value spec) wrong-type #{}))))))
