(ns rainbow.math.rational.nnrat.farkas-row-reconstruction-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.nnrat.farkas-row-reconstruction :as reconstruction]))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (reconstruction/extend-environment (:environment checkpoint)))))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "Reconstruction test expression failed elaboration" {:result r})))
    (:term r)))
(defn- check [env value type]
  (kernel/check env (elaborate! env value) (elaborate! env type) #{}))

(deftest reverse-row-transports-are-kernel-checked-and-axiom-free
  (let [env @checked-environment
        ids (reconstruction/theorem-ids env)]
    (is (= #{'nnrat/farkas-lower-to-both-sides 'nnrat/farkas-upper-to-both-sides}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{}))))
        (is (= #{} (kernel/axioms env id)))))))

(deftest unchanged-reduced-proof-cannot-stand-in-for-reconstruction
  (let [env @checked-environment]
    (doseq [spec reconstruction/theorem-specs]
      ;; Preserve the exact lambda binders and replace the entire proof body
      ;; with the reduced-row hypothesis. This must fail at the kernel.
      (let [candidate (assoc (:value spec) 2 'reduced)]
        (is (= :rejected (:status (check env candidate (:type spec))))
            (str "Direct hypothesis passthrough must fail for " (:name spec)))))))

(deftest difference-equation-is-checked-at-the-call-site
  (let [env @checked-environment
        z (f/const* 'nnrat/zero [])
        one (f/const* 'nnrat/one [])
        ;; Use b=a+d literally, avoiding any extra numeral-normalization lemma.
        sum (app 'nnrat/add z one)
        d-good (app 'nnrat/equivalent-reflexive sum)
        d-bad (app 'nnrat/equivalent-reflexive z)
        p (app 'nnrat/add (app 'nnrat/multiply one one) z)
        lower-proof (app 'nnrat/at-most-reflexive p)
        lower-goal (app 'nnrat/at-most (app 'nnrat/add (app 'nnrat/multiply z one) p)
                        (app 'nnrat/add (app 'nnrat/multiply sum one) z))
        lower-call (fn [diff] (app 'nnrat/farkas-lower-to-both-sides
                                  z sum one p z one diff lower-proof))
        ;; Upper case uses q=d*v+p, so the reduced premise is reflexive.
        q (app 'nnrat/add (app 'nnrat/multiply one one) z)
        upper-proof (app 'nnrat/at-most-reflexive q)
        upper-goal (app 'nnrat/at-most (app 'nnrat/add (app 'nnrat/multiply sum one) z)
                        (app 'nnrat/add (app 'nnrat/multiply z one) q))
        upper-call (fn [diff] (app 'nnrat/farkas-upper-to-both-sides
                                  sum z one z q one diff upper-proof))]
    (doseq [[call goal] [[lower-call lower-goal] [upper-call upper-goal]]]
      (is (= :checked (:status (check env (call d-good) goal))))
      (is (= :rejected (:status (check env (call d-bad) goal)))))))
