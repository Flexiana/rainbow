(ns rainbow.math.finite.index-hastings-coefficient-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.finite.index-hastings-coefficient :as target]))

(def checked-environment
  (delay
    (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status cp)) (throw (ex-info "D63 replay failed" {})))
      (target/extend-environment (:environment cp)))))

(deftest canonical-hastings-factor-is-checked-and-axiom-free
  (let [env @checked-environment ids (merge (target/definition-ids env) (target/theorem-ids env))]
    (is (= #{'mcmc/nnrat-hastings-index-contraction-factor
             'mcmc/nnrat-hastings-index-contraction-factor-proper
             'mcmc/nnrat-hastings-index-dobrushin-bound-of-full-support} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{}))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (prn {:hastings-coefficient-ids ids})))

(defn- c [name] (f/const* name []))
(defn- app [name & xs] (apply f/app (c name) xs))
(defn- poly [name & xs] (apply f/app (f/const* name [[:zero]]) xs))
(def nat (c 'data/Nat))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) (c 'data/zero)) n))
(defn- rat [n d] (app 'nnrat/make (numeral n) (numeral (dec d))))
(defn- refl [A x] (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) A x))
(defn- check [proof statement]
  (let [env @checked-environment
        core (fn [s] (let [r (elaborate/core-expression env s)]
                       (when-not (= :elaborated (:status r)) (throw (ex-info "Example elaboration failed" r)))
                       (:term r)))]
    (binding [kernel/*reduction-budget* 4000000]
      (kernel/check env (core proof) (core statement) #{}))))

(deftest concrete-hastings-certificates-reject-false-input-certificates
  (doseq [[label size target-n proposal-n proposal-d expected]
           [[:singleton 1 1 1 1 :checked]
            [:two-states-unnormalized-target 2 1 1 2 :checked]
            [:false-full-support 1 0 1 1 :rejected]
            [:false-proposal-normalization 1 1 2 1 :rejected]]]
    (let [previous (numeral (dec size)) upper (numeral size)
          element (app 'finite/Index upper) states (app 'finite/index-finset upper)
          weights (f/lam [['i element]] (rat target-n 1))
          proposal (f/lam [['i element] ['j element]] (rat proposal-n proposal-d))
          row-total (poly 'probability/nnrat-total-mass element states (f/app proposal 'i))
          normalized (f/lam [['i element]]
                       (refl nat (app 'nat/multiply (app 'nnrat/numerator row-total)
                                      (app 'nnrat/denominator (c 'nnrat/one)))))
          decision (app 'finite/index-decide-equality upper)
          kernel (poly 'mcmc/nnrat-hastings-canonical-kernel element states weights proposal decision)
          anchor (app 'finite/index-last previous)
          minimum (poly 'markov/nnrat-kernel-minimum element states kernel anchor anchor)
          dp (app 'nnrat/denominator-predecessor minimum)
          factor (app 'nnrat/make dp dp)
          proof (app 'mcmc/nnrat-hastings-index-dobrushin-bound-of-full-support
                     previous weights proposal normalized (refl (c 'data/Bool) (c 'data/true)))
          statement (app 'signed/at-most
                         (poly 'markov/signed-kernel-dobrushin-coefficient element states kernel)
                         (app 'signed/from-nnrat factor))]
      (is (= expected (:status (check proof statement))) (str label))
      (when (= :checked expected)
        (is (= :checked (:status (check
                                  (app 'mcmc/nnrat-hastings-index-contraction-factor-proper previous weights proposal)
                                  (app 'nat/at-most (app 'nnrat/numerator factor)
                                       (app 'nnrat/denominator-predecessor factor))))) (str label))))))
