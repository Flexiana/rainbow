(ns rainbow.math.rational.signed.square-convex-test
  "Gate for square convexity: the variance identity and signed/square-convex are
  kernel-checked and axiom-free, and a tampered variance identity (dropping the
  nonnegative variance term, which would collapse the identity to the false
  csq ~ rhs) is rejected by the kernel -- the discrimination control."
  (:require [clojure.test :refer [deftest is]]
            [clojure.walk :as walk]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.square-convex :as sc]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (sc/extend-environment (:environment checkpoint)))))

(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "expression failed elaboration" {:result r})))
    (:term r)))

(defn- check [env value type universes]
  (kernel/check env (elaborate! env value) (elaborate! env type) universes))

(deftest square-convexity-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (sc/theorem-ids env)]
    (is (= #{'signed/multiply-cross-regroup 'signed/square-combination-expand
             'signed/variance-term-expand 'signed/variance-sum-collapse
             'signed/variance-identity 'signed/square-convex}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest variance-identity-without-the-variance-term-is-rejected
  (let [env @checked-environment
        spec sc/variance-identity-spec
        ;; The proof establishes  csq + w0*w1*(x-y)^2 ~ rhs.  Replace the whole
        ;; (add csq var) left-hand side with just csq -- i.e. claim csq ~ rhs,
        ;; which is false whenever x != y.  The kernel must reject.
        variance-subterm
        (f/app (f/const* 'signed/multiply [])
               (f/app (f/const* 'signed/multiply [])
                      (f/app (f/const* 'signed/from-nnrat []) 'w0)
                      (f/app (f/const* 'signed/from-nnrat []) 'w1))
               (f/app (f/const* 'signed/multiply [])
                      (f/app (f/const* 'signed/subtract []) 'x 'y)
                      (f/app (f/const* 'signed/subtract []) 'x 'y)))
        ;; Find the (add csq var) node in the type and swap it to csq alone by
        ;; replacing var with signed/zero (csq + 0 ~ rhs still forces csq ~ rhs).
        wrong-type (walk/postwalk-replace
                    {variance-subterm (f/const* 'signed/zero [])}
                    (:type spec))]
    (is (not= (:type spec) wrong-type))
    (is (= :rejected (:status (check env (:value spec) wrong-type #{}))))))
