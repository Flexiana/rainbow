(ns rainbow.math.rational.signed.scale-reflection-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.order-nontrivial :as nontrivial]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.logic.proposition :as p]
            [rainbow.math.rational.signed.scale-reflection :as reflection]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(def ^:private zero (f/const* 'nnrat/zero []))
(def ^:private one (f/const* 'nnrat/one []))
(def ^:private nz (f/const* 'data/zero []))
(def ^:private sz (app 'signed/make zero zero))
(def ^:private so (app 'signed/make one zero))
(defn- scale [c x] (app 'signed/scale c x))
(defn- le [x y] (app 'signed/at-most x y))

;; Formal counterexample to admitting a zero scale: 0*1 <= 0*0, but not 1 <= 0.
(def ^:private zero-scale-hides-unit-gap-spec
  {:name 'audit/zero-scale-hides-signed-unit-gap :universes []
   :type (le (scale zero so) (scale zero sz))
   :value
   (let [l (ring/radd (ring/rmul zero one) (ring/rmul zero zero))
         r (ring/radd (ring/rmul zero zero) (ring/rmul zero zero))]
     ;; Closed zero numerators reduce directly; the ring tactic intentionally
     ;; treats named zero/one constants as atoms, not numerical identities.
     (app 'nnrat/equivalent-to-at-most l r (app 'nnrat/equivalent-reflexive l)))})
(def ^:private signed-unit-gap-impossible-spec
  {:name 'audit/signed-unit-gap-impossible :universes []
   :type (p/negation (le so sz))
   :value
   (f/lam [['ordered (le so sz)]]
          (app 'nnrat/one-not-at-most-zero
               (app 'nnrat/at-most-add-right-cancel one zero zero 'ordered)))})

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (-> (:environment checkpoint)
          reflection/extend-environment
          nontrivial/extend-environment
          (support/extend-with ::counterexample
                               [zero-scale-hides-unit-gap-spec
                                signed-unit-gap-impossible-spec])))))

(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "Scaling control failed elaboration" {:result r})))
    (:term r)))
(defn- check [env value type]
  (kernel/check env (elaborate! env value) (elaborate! env type) #{}))

(deftest reflection-transport-and-zero-counterexample-are-axiom-free
  (let [env @checked-environment]
    (is (= #{'signed/scale-positive-reflects-order 'signed/scaled-bound-to-original}
           (set (keys (reflection/theorem-ids env)))))
    (doseq [spec (concat reflection/theorem-specs
                        [zero-scale-hides-unit-gap-spec signed-unit-gap-impossible-spec])]
      (let [id (environment/resolve-id env (:name spec))
            d (environment/declaration env id)]
        (is (some? id))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{}))))
        (is (= #{} (kernel/axioms env id)))))))

(deftest scaled-hypothesis-passthrough-is-not-reflection
  (let [env @checked-environment]
    (doseq [[spec body] [[reflection/scale-positive-reflects-order-spec 'ordered]
                       [reflection/scaled-bound-to-original-spec 'checked-bound]]]
      (is (= :rejected (:status (check env (assoc (:value spec) 2 body) (:type spec))))))))

(deftest endpoint-equivalences-are-checked-at-the-call-site
  (let [env @checked-environment
        ;; Positive scale 2/3 and arbitrary signed x exercise both cross sums.
        c (app 'nnrat/make (app 'data/succ (app 'data/succ nz))
               (app 'data/succ (app 'data/succ nz)))
        ap (app 'data/succ nz)
        adp (app 'data/succ (app 'data/succ nz))
        sx (scale c 'x)
        eq-proof (app 'nnrat/equivalent-reflexive
                      (ring/radd (app 'signed/positive sx) (app 'signed/negative sx)))
        wrong-eq (app 'nnrat/equivalent-reflexive zero)
        goal (f/forall [['x reflection/signed]] (le 'x 'x))
        candidate (fn [left-same right-same]
                    (f/lam [['x reflection/signed]]
                           (app 'signed/scaled-bound-to-original ap adp 'x 'x sx sx
                                left-same right-same (app 'signed/at-most-reflexive sx))))]
    (is (= :checked (:status (check env (candidate eq-proof eq-proof) goal))))
    (is (= :rejected (:status (check env (candidate wrong-eq eq-proof) goal))))
    (is (= :rejected (:status (check env (candidate eq-proof wrong-eq) goal))))))
