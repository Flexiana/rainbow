(ns rainbow.nnrat-farkas-vector-substantive-guard-test
  "POSITIVE regression guard for the LP Fourier-Motzkin lane's SUBSTANTIVE
  theorems -- the complement of nnrat_farkas_vector_vacuity_test.clj.

  The vacuity audit (part 2) found that
  none of the lane's substantive theorems is PASSTHROUGH-inhabited: for none of
  them does returning one of its own hypotheses inhabit the conclusion. That is
  a necessary condition for non-vacuity -- if a theorem's conclusion is defeq
  one of its hypotheses, the theorem is trivially true and its gate cannot fail.
  Nothing enforced that result until now.

  This test freezes it: for each substantive theorem, for each argument, it
  builds the passthrough candidate (a lambda over the theorem's own domains
  returning that argument) and asserts the kernel REJECTS it. Pure core-term
  construction from the declared type -- no elaboration, no proof rewrite.

  POLARITY IS NORMAL here (unlike the vacuity file): PASS = the theorem still
  resists passthrough (good). A FAILURE means some theorem's conclusion became
  defeq one of its hypotheses -- i.e. it was weakened to triviality; the message
  names the theorem and the argument. Note this guards ONE vacuity mode
  (conclusion == hypothesis); it is a necessary check, not a proof of
  substantiveness (see the report's method-asymmetry note). The five KNOWN-
  vacuous theorems are deliberately excluded -- two of them (feasible-step,
  eliminate) ARE passthrough-inhabited via the identity, which the vacuity file
  already records."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-step :as vector-step]
            [rainbow.math.rational.nnrat.farkas-partition-list :as partition-list]
            [rainbow.math.rational.nnrat.farkas-eliminate-base :as eliminate-base]
            [rainbow.math.rational.nnrat.farkas-vector-both-sides :as vector-both-sides]
            [rainbow.math.rational.nnrat.farkas-vector-partition-pack :as partition-pack]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector-step/extend-environment
          partition-list/extend-environment
          eliminate-base/extend-environment
          vector-both-sides/extend-environment
          partition-pack/extend-environment))))

;; the lane's SUBSTANTIVE theorems (the five known-vacuous ones are excluded)
(def ^:private substantive-theorems
  '[nnrat/farkas-eliminate-base
    nnrat/farkas-eliminate-all
    nnrat/farkas-vector-both-sides-to-lower
    nnrat/farkas-vector-both-sides-to-upper
    nnrat/farkas-vector-both-sides-reduce
    nnrat/farkas-vector-partition-pack
    nnrat/farkas-vector-partition-fold
    nnrat/farkas-vector-adapter-list
    nnrat/farkas-vector-adapter-bilist
    nnrat/farkas-vector-input-rows-append
    nnrat/farkas-cross-vectors
    nnrat/farkas-cross-vectors-reduced-holds
    nnrat/farkas-cross-vectors-all-reduced])

(defn- decl-type [env name]
  (:rainbow/type (environment/declaration env (environment/resolve-id env name))))

;; collect the Pi-spine domains of a type
(defn- pi-domains [t]
  (loop [t t ds []]
    (if (and (vector? t) (= :pi (first t)))
      (recur (nth t 2) (conj ds (nth t 1)))
      ds)))

;; nested lambda over the given domains returning the given body
(defn- mk-lam [domains body]
  (reduce (fn [b d] [:lam d b :explicit]) body (reverse domains)))

;; does returning argument i (0-indexed from the outside) inhabit the type?
(defn- passthrough-checks? [env t i n]
  (= :checked (:status (kernel/check env (mk-lam (pi-domains t) [:bound (dec (- n i))]) t #{}))))

(deftest substantive-theorems-reject-passthrough
  (testing "no substantive lane theorem is inhabited by returning one of its
            own hypotheses (conclusion is not defeq any hypothesis). A FAILURE
            names a theorem that was weakened to triviality."
    (let [env @checked-environment]
      (doseq [nm substantive-theorems]
        (let [id (environment/resolve-id env nm)]
          (is (some? id) (str nm " is not present in the environment"))
          (when id
            (let [t (decl-type env nm)
                  n (count (pi-domains t))]
              (is (pos? n) (str nm " has no hypotheses to passthrough-test"))
              (doseq [i (range n)]
                (is (not (passthrough-checks? env t i n))
                    (str nm ": returning argument " i " now inhabits the "
                         "conclusion -- the conclusion became defeq that "
                         "hypothesis, so the theorem was weakened to triviality. "
                         "Check the change against the design notes."))))))))))
