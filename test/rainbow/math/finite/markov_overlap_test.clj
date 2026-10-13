(ns rainbow.math.finite.markov-overlap-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.nnrat.map-sum-member :as member-sum]
            [rainbow.math.rational.nnrat.unit-fraction :as unit]
            [rainbow.math.finite.markov-positive-coefficient :as positive-coefficient]
            [rainbow.math.finite.markov-overlap :as target]))
(def checked-environment (delay
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
    (when-not (= :replayed (:status cp)) (throw (ex-info "D63 replay failed" {})))
    (positive-coefficient/extend-environment (:environment cp)))))
(deftest overlap-identities-and-coefficient-certificate-are-kernel-checked
  (let [env @checked-environment ids (target/theorem-ids env)]
    (is (= 6 (count ids)))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
        (is (= #{} (kernel/axioms env id)))))))

(deftest coefficient-budget-keeps-two-independent-row-indices
  ;; Independent interface construction: the summation column must never
  ;; capture either row variable in the supplied row-pair budget.
  (let [u [:param 'u]
        call (fn [name & xs] (apply f/app (f/const* name []) xs))
        poly (fn [name & xs] (apply f/app (f/const* name [u]) xs))
        rat (f/const* 'nnrat/NonnegativeRational [])
        one (f/const* 'nnrat/one [])
        enumeration (poly 'finset-data/enumeration 'X 'xs)
        member (fn [x] (poly 'list/membership 'X enumeration x))
        common (poly 'probability/nnrat-total-mass 'X 'xs
                 (f/lam [['column 'X]]
                   (call 'minmax/min (f/app 'K 'row-a 'column) (f/app 'K 'row-b 'column))))
        budget (f/forall [['row-a 'X] ['a-member (member 'row-a)]
                          ['row-b 'X] ['b-member (member 'row-b)]]
                 (call 'nnrat/at-most one (call 'nnrat/add 'rate common)))
        expected (f/forall [['X [:sort [:succ u]]]
                            ['xs (poly 'finset-data/Finset 'X)] ['K (f/arrow 'X 'X rat)]
                            ['rows (poly 'markov/nnrat-kernel-rows-normalized 'X 'xs 'K)]
                            ['rate rat] ['budget budget]]
                   (call 'signed/at-most (poly 'markov/signed-kernel-dobrushin-coefficient 'X 'xs 'K)
                         (call 'signed/from-nnrat 'rate)))
        env @checked-environment
        proof (elaborate/core-expression env
                (f/const* 'markov/signed-kernel-dobrushin-at-most-of-common-mass [u]))
        statement (elaborate/core-expression env expected)]
    (is (= [:elaborated :elaborated] [(:status proof) (:status statement)]))
    (is (= :checked (:status (kernel/check env (:term proof) (:term statement) #{'u}))))))

(deftest member-to-sum-bound-is-kernel-checked-and-axiom-free
  (let [env @checked-environment ids (member-sum/theorem-ids env)]
    (is (= #{'nnrat/map-sum-at-least-member} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest unit-fraction-construction-is-kernel-checked-and-axiom-free
  (let [env @checked-environment ids (unit/theorem-ids env)]
    (is (= #{'nnrat/unit-fraction-at-most-positive 'nnrat/unit-fraction-positive
             'nnrat/unit-fraction-plus-complement 'nnrat/unit-fraction-complement-proper}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{}))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (prn {:unit-fraction-theorem-ids ids})))

(deftest positive-minimum-coefficient-composition-is-kernel-checked-and-axiom-free
  (let [env @checked-environment ids (positive-coefficient/theorem-ids env)]
    (is (= #{'markov/signed-kernel-dobrushin-at-most-of-positive-minimum
             'markov/signed-kernel-dobrushin-at-most-of-listed-positive}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (prn {:positive-coefficient-theorem-ids ids})))

(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def nat (c 'data/Nat))
(def nnrat (c 'nnrat/NonnegativeRational))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) (c 'data/zero)) n))
(defn- rational [n d] (app 'nnrat/make (numeral n) (numeral (dec d))))
(defn- row [a b]
  (f/lam [['n nat]]
    (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
      (f/lam [['ignored nat]] nnrat) a
      (f/lam [['previous nat] ['acc nnrat]] b) 'n)))
(def states (app 'finset-data/range (numeral 2)))
(defn- total [mass] (poly 'probability/nnrat-total-mass nat states mass))
(defn- rational-equality [a b]
  (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat
    (app 'nat/multiply (app 'nnrat/numerator a) (app 'nnrat/denominator b))))
(defn- check [proof statement]
  (let [env @checked-environment
        core (fn [surface]
               (let [r (elaborate/core-expression env surface)]
                 (when-not (= :elaborated (:status r)) (throw (ex-info "Overlap example elaboration failed" r)))
                 (:term r)))]
    (binding [kernel/*reduction-budget* 4000000]
      (kernel/check env (core proof) (core statement) #{}))))

(defn- nat-list [values]
  (reduce (fn [tail head]
            (f/app (f/const* 'data/cons [[:succ [:zero]]]) nat (numeral head) tail))
          (f/app (f/const* 'data/nil [[:succ [:zero]]]) nat)
          (reverse values)))

(deftest explicit-unit-fraction-lower-bounds-reject-zero-positivity
  (doseq [[n d expected] [[1 1 :checked] [1 2 :checked] [2 2 :checked]
                         [3 2 :checked] [1 4 :checked] [0 2 :rejected]]]
    (let [value (rational n d)
          epsilon (unit/unit-fraction (app 'nnrat/denominator-predecessor value))
          predicate (f/lam [['extra nat]]
                      (f/equality [:succ [:zero]] nat
                        (app 'algebra/nat-add (numeral 1) 'extra) (numeral n)))
          positivity (f/app (f/const* 'proposition/witness [[:succ [:zero]]]) nat predicate
                       (numeral (max 0 (dec n)))
                       (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat (numeral n)))
          proof (app 'nnrat/unit-fraction-at-most-positive value positivity)]
      (is (= expected (:status (check proof (app 'nnrat/at-most epsilon value)))) (str [n d])))))

(deftest explicit-complements-cover-zero-and-nonzero-proper-factors
  (doseq [dp [0 1 2 3]]
    (let [previous (numeral dp) epsilon (unit/unit-fraction previous)
          rho (unit/proper-complement previous)]
      (is (= :checked (:status (check (app 'nnrat/unit-fraction-plus-complement previous)
                                     (app 'nnrat/equivalent (app 'nnrat/add rho epsilon) (c 'nnrat/one))))))
      (is (= :checked (:status (check (app 'nnrat/unit-fraction-complement-proper previous)
                                     (app 'nat/at-most (app 'nnrat/numerator rho)
                                          (app 'nnrat/denominator-predecessor rho)))))))))

(defn- membership-proof [values selected position]
  (let [left (f/equality [:succ [:zero]] nat (numeral selected) (numeral (first values)))
        right (poly 'list/membership nat (nat-list (rest values)) (numeral selected))]
    (if (zero? position)
      (app 'proposition/left-disjunct left right
        (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat (numeral selected)))
      (app 'proposition/right-disjunct left right
        (membership-proof (rest values) selected (dec position))))))

(deftest positive-kernel-coefficient-construction-checks-anchors-and-normalization
  (doseq [[label n d source target expected]
           [[:uniform 1 2 0 0 :checked]
            [:noncanonical-uniform 2 4 0 0 :checked]
            [:false-normalization 1 1 0 0 :rejected]
            [:zero-violates-positivity-and-normalization 0 2 0 0 :rejected]
            [:false-source-anchor 1 2 2 0 :rejected]
            [:false-target-anchor 1 2 0 2 :rejected]]]
    (let [value (rational n d)
          transition (f/lam [['source nat] ['target nat]] value)
          items (poly 'finset-data/enumeration nat states)
          member (fn [i] (poly 'list/membership nat items i))
          positive-predicate (f/lam [['extra nat]]
                               (f/equality [:succ [:zero]] nat
                                 (app 'algebra/nat-add (numeral 1) 'extra) (numeral n)))
          positive (f/app (f/const* 'proposition/witness [[:succ [:zero]]]) nat positive-predicate
                     (numeral (max 0 (dec n)))
                     (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat (numeral n)))
          listed-positive (f/lam [['i nat] ['j nat] ['i-member (member 'i)] ['j-member (member 'j)]] positive)
          m (poly 'markov/nnrat-kernel-minimum nat states transition (numeral source) (numeral target))
          dp (app 'nnrat/denominator-predecessor m)
          rho (unit/proper-complement dp)
          proof (poly 'markov/signed-kernel-dobrushin-at-most-of-listed-positive
                  nat states transition
                  (f/lam [['i nat]] (rational-equality (total (f/app transition 'i)) (c 'nnrat/one)))
                  (numeral source) (numeral target)
                  (membership-proof [1 0] source 1) (membership-proof [1 0] target 1) listed-positive)
          statement (app 'signed/at-most
                         (poly 'markov/signed-kernel-dobrushin-coefficient nat states transition)
                         (app 'signed/from-nnrat rho))]
      (is (= expected (:status (check proof statement))) (str label))
      (when (= :checked expected)
        (is (= :checked (:status (check (app 'nnrat/unit-fraction-complement-proper dp)
                                       (app 'nat/at-most (app 'nnrat/numerator rho)
                                            (app 'nnrat/denominator-predecessor rho))))) (str label))
        (let [expected-factor (rational (dec d) d)]
          (is (= :checked (:status (check (rational-equality rho expected-factor)
                                         (app 'nnrat/equivalent rho expected-factor)))) (str label)))))))

(deftest member-bound-handles-head-tail-duplicates-and-rejects-false-membership
  (let [z (rational 0 1) o (rational 1 1) two (rational 2 1)]
    (doseq [[label values selected position mapping status]
            [[:head [0 1] 0 0 (row o two) :checked]
             [:tail [0 1] 1 1 (row o two) :checked]
             [:duplicate [1 1] 1 1 (row o two) :checked]
             [:zero [0 1] 0 0 (row z z) :checked]
             [:noncanonical [0 1] 1 1 (row (rational 0 2) (rational 2 2)) :checked]
             [:not-listed [0] 1 0 (row z two) :rejected]]]
      (let [items (nat-list values)
            proof (poly 'nnrat/map-sum-at-least-member nat mapping items (numeral selected)
                    (membership-proof values selected position))
            statement (app 'nnrat/at-most (f/app mapping (numeral selected))
                           (poly 'nnrat/map-sum nat mapping items))]
        (is (= status (:status (check proof statement))) (str label))))))

(deftest listed-column-lower-bound-requires-both-rows
  (let [z (rational 0 1) o (rational 1 1) half (rational 1 2)]
    (doseq [[label left right epsilon status]
            [[:shared-half (row half half) (row half half) half :checked]
             [:shared-unit (row o z) (row o z) o :checked]
             [:zero (row z o) (row z o) z :checked]
             [:false-right-bound (row o z) (row z o) o :rejected]
             [:false-left-bound (row z o) (row o z) o :rejected]]]
      (let [target (numeral 0)
            lower (fn [value]
                    (app 'nnrat/equivalent-to-at-most epsilon value (rational-equality epsilon value)))
            proof (poly 'markov/nnrat-common-total-at-least-listed-term
                    nat states left right target (membership-proof [1 0] 0 1) epsilon
                    (lower (f/app left target)) (lower (f/app right target)))
            overlap (total (f/lam [['i nat]] (app 'minmax/min (f/app left 'i) (f/app right 'i))))]
        (is (= status (:status (check proof (app 'nnrat/at-most epsilon overlap)))) (str label))))))

(deftest shared-column-certifies-coefficient-and-checks-each-premise
  (let [z (rational 0 1) o (rational 1 1) half (rational 1 2)]
    (doseq [[label mass epsilon rho target status]
            [[:uniform (row half half) half half 0 :checked]
             [:point-mass (row o z) o z 0 :checked]
             [:false-budget (row half half) half z 0 :rejected]
             [:false-column-bound (row half half) o z 0 :rejected]
             [:false-normalization (row o o) o z 0 :rejected]
             [:false-target-membership (row half half) half half 2 :rejected]]]
      (let [transition (f/lam [['source nat]] mass)
            listed (poly 'list/membership nat (poly 'finset-data/enumeration nat states) 'i)
            column-entry (f/app transition 'i (numeral target))
            budget (app 'nnrat/add rho epsilon)
            proof (poly 'markov/signed-kernel-dobrushin-at-most-of-shared-column
                    nat states transition
                    (f/lam [['i nat]] (rational-equality (total (f/app transition 'i)) o))
                    (numeral target) (membership-proof [1 0] target 1) epsilon rho
                    (f/lam [['i nat] ['i-member listed]]
                      (app 'nnrat/equivalent-to-at-most epsilon column-entry
                        (rational-equality epsilon column-entry)))
                    (app 'nnrat/equivalent-to-at-most o budget (rational-equality o budget)))
            statement (app 'signed/at-most
                           (poly 'markov/signed-kernel-dobrushin-coefficient nat states transition)
                           (app 'signed/from-nnrat rho))]
        (is (= status (:status (check proof statement))) (str label))))))

(deftest overlap-identity-includes-unnormalized-and-noncanonical-masses
  (let [z (rational 0 1) o (rational 1 1) two (rational 2 1)
        half (rational 1 2)]
    (doseq [[label left right expected status]
            [[:identical (row o z) (row o z) o :checked]
             [:disjoint (row o z) (row z o) o :checked]
             [:partially-shared (row o z) (row half half) o :checked]
             [:unnormalized (row two z) (row z two) two :checked]
             [:noncanonical (row o z) (row (rational 2 2) (rational 0 2)) o :checked]
             [:zero (row z z) (row z z) z :checked]
             ;; Here TV + common = 1/2, while the left total is 1.
             ;; Attempting to supply false equal-total evidence must fail.
             [:unequal-total (row o z) (row z z) o :rejected]]]
      (let [overlap (total (f/lam [['i nat]] (app 'minmax/min (f/app left 'i) (f/app right 'i))))
            lhs (app 'nnrat/add (poly 'markov/nnrat-normalized-total-variation nat states left right) overlap)
            proof (app 'nnrat/equivalent-transitive lhs (total left) expected
                    (poly 'markov/nnrat-normalized-tv-plus-common-total nat states left right
                          (rational-equality (total left) (total right)))
                    (rational-equality (total left) expected))]
        (is (= status (:status (check proof (app 'nnrat/equivalent lhs expected)))) (str label))))))

(deftest shared-mass-budgets-accept-sharp-bounds-and-reject-understatements
  (let [z (rational 0 1) o (rational 1 1) half (rational 1 2) left (row o z)]
    (doseq [[label right rho status]
            [[:identical (row o z) z :checked]
             [:disjoint (row z o) o :checked]
             [:half-overlap (row half half) half :checked]
             [:false-zero-bound (row z o) z :rejected]
             [:false-normalization (row (rational 2 1) z) z :rejected]]]
      (let [overlap (total (f/lam [['i nat]] (app 'minmax/min (f/app left 'i) (f/app right 'i))))
            budget (app 'nnrat/add rho overlap)
            proof (poly 'markov/nnrat-normalized-tv-at-most-of-common-mass nat states left right
                        (rational-equality (total left) o) (rational-equality (total right) o) rho
                        (app 'nnrat/equivalent-to-at-most o budget (rational-equality o budget)))
            statement (app 'nnrat/at-most
                           (poly 'markov/nnrat-normalized-total-variation nat states left right) rho)]
        (is (= status (:status (check proof statement))) (str label))))))
