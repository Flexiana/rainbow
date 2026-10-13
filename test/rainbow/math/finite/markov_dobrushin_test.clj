(ns rainbow.math.finite.markov-dobrushin-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.finite.markov-dobrushin :as dobrushin]))
(def checked-environment
  (delay (let [checkpoint (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status checkpoint)) (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
           (dobrushin/extend-environment (:environment checkpoint)))))
(deftest coefficient-definition-is-well-formed-and-axiom-free
  (testing "the finite coefficient definition is registered and kernel-checks"
    (let [env @checked-environment ids (dobrushin/definition-ids env)]
      (is (= 1 (count ids)))
      (doseq [[name id] ids]
        (let [d (environment/declaration env id)]
          (is (some? d) (str name))
          (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d))))) (str name))
          (is (= #{} (kernel/axioms env id)) (str name)))))))

(deftest coefficient-nonnegative-is-kernel-checked
  (let [env @checked-environment
        id (get (dobrushin/theorem-ids env)
                'markov/signed-dobrushin-coefficient-nonnegative)
        declaration (environment/declaration env id)]
    (is (some? id))
    (is (= :checked (:status (kernel/check env (:rainbow/value declaration)
                                          (:rainbow/type declaration)
                                          (set (:rainbow/universes declaration))))))
    (is (= #{} (kernel/axioms env id)))))

(deftest coefficient-empty-is-kernel-checked
  (let [env @checked-environment
        id (get (dobrushin/theorem-ids env)
                'markov/signed-dobrushin-coefficient-empty)
        declaration (environment/declaration env id)]
    (is (some? id))
    (is (= :checked (:status (kernel/check env (:rainbow/value declaration)
                                          (:rainbow/type declaration)
                                          (set (:rainbow/universes declaration))))))
    (is (= #{} (kernel/axioms env id)))))

(deftest contraction-evidence-points-to-the-separate-checked-producer
  (testing "metadata names the proof producer; it does not itself supply a proof"
    (let [target dobrushin/markov-contraction-statement]
      (is (= :theorem-evidence (:kind target)))
      (is (= :proved (:status target)))
      (is (= 'markov/nnrat-dobrushin-contraction (:proof-theorem target)))
      (is (= :total-variation-contraction (:conclusion target)))
      (is (= ["0 <= delta(K)" "delta(K) <= 1"] (:coefficient-bounds target)))
      (is (= ["0 <= delta(K)" "delta(K) <= 1"] (:proved-coefficient-bounds target)))
      (is (some #{:dobrushin-coefficient-at-most-rho} (:hypotheses target))))))

(deftest conditional-bounds-are-kernel-checked-and-axiom-free
  (let [env @checked-environment]
    (doseq [name ['markov/signed-dobrushin-coefficient-bounded
                  'markov/signed-dobrushin-coefficient-at-most-one-of-pointwise]]
      (let [id (get (dobrushin/theorem-ids env) name)
            declaration (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value declaration)
                                              (:rainbow/type declaration)
                                              (set (:rainbow/universes declaration)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest arbitrary-distance-lists-do-not-have-an-unconditional-unit-bound
  (let [env @checked-environment
        c #(function/const* % [])
        app function/app
        two (app (c 'nnrat/add) (c 'nnrat/one) (c 'nnrat/one))
        singleton (app (function/const* 'data/cons [dobrushin/type-level])
                       dobrushin/nnrat two
                       (app (function/const* 'data/nil [dobrushin/type-level])
                            dobrushin/nnrat))
        coefficient (app (function/const* 'markov/signed-dobrushin-coefficient
                                            [dobrushin/U]) 'S singleton)
        bindings [['S dobrushin/type-u]]
        false-bound (function/forall bindings
                      (app (c 'signed/at-most) coefficient (c 'signed/one)))
        wrong-proof (function/lam bindings (c 'signed/zero-at-most-one))
        type-result (elaborate/core-expression env false-bound)
        value-result (elaborate/core-expression env wrong-proof)]
    (is (= :elaborated (:status type-result)))
    (is (= :elaborated (:status value-result)))
    (is (= :rejected (:status (kernel/check env (:term value-result)
                                           (:term type-result) #{'u}))))))

(deftest contraction-target-handles-normalization-and-mass-counterexamples
  ;; Independent exact-rational calculations, not machine-checked theorems.
  (let [l1 (fn [a b] (reduce + (map #(abs (- %1 %2)) a b)))
        tv (fn [a b] (/ (l1 a b) 2))
        identical-rows [[1 0] [1 0]]
        push-forward (fn [mass]
                       (mapv (fn [j] (reduce + (map #(* %1 (nth %2 j))
                                                    mass identical-rows)))
                             (range 2)))
        target dobrushin/markov-contraction-statement]
    ;; Disjoint stochastic rows have L1 distance 2, normalized TV distance 1.
    (is (= 2 (l1 [1 0] [0 1])))
    (is (= 1 (tv [1 0] [0 1])))
    ;; delta=0 for identical rows, but unequal total masses remain separated.
    (is (zero? (apply tv identical-rows)))
    (is (= 1/2 (tv (push-forward [1 0]) (push-forward [0 0]))))
    (is (some #{:equal-total-mass} (:hypotheses target)))
    (is (= :half-l1 (:distance-convention target)))
    (is (= :l1 (:kernel-distance-convention target)))))

(deftest coefficient-bound-obligations-remain-explicit
  (testing "coefficient obligations point to their checked producers"
    (let [obligations dobrushin/dobrushin-coefficient-bound-obligations]
      (is (= 2 (count obligations)))
      (is (= [:proved :proved] (mapv :status obligations)))
      (is (= ["0 <= delta(K)" "delta(K) <= 1"]
             (mapv :statement obligations)))
      (is (= 'list/signed-map-max-nonnegative
             (:required-lemma (first obligations))))
      (is (nil? (:elaboration-gap (first obligations)))))))

(deftest coefficient-upper-bound-route-is-explicit
  (let [upper (second dobrushin/dobrushin-coefficient-bound-obligations)]
    (is (= 'list/signed-map-max-bounded (:required-lemma upper)))
    (is (= 'rainbow.math.rational.signed.geometric-bridge (:required-provider upper)))
    (is (= [:nnrat-row-distance-at-most-one
            'signed/from-nnrat-at-most
            :pointwise-bound-on-enumerated-rows]
           (:sub-obligations upper)))
    (is (nil? (:elaboration-gap upper)))))

(deftest coefficient-proof-plan-identifies-constructive-route
  (testing "the constructive proof plan is discharged"
    (let [plan dobrushin/dobrushin-coefficient-proof-plan]
      (is (= :proved (:status plan)))
      (is (= :successor-universe-list (:carrier-specialization plan)))
      (is (= 'list/signed-map-max-nonnegative (:nonnegative-step plan)))
      (is (= 'markov/row-total-variation-at-most-one (:upper-bound-step plan)))
      (is (nil? (:current-gap plan))))))

(deftest coefficient-universe-bridge-is-explicit
  (let [bridge dobrushin/dobrushin-list-universe-bridge]
    (is (= :nnrat (:coefficient-element bridge)))
    (is (= :zero (:coefficient-element-universe bridge)))
    (is (= :succ-zero (:coefficient-list-level bridge)))
    (is (= :zero (:bounded-lemma-specialization bridge)))
    (is (= :proved (:status bridge)))
    (is (some? (get (dobrushin/theorem-ids @checked-environment)
                    (:theorem bridge))))))
