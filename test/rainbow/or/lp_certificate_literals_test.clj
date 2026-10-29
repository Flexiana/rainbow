(ns rainbow.or.lp-certificate-literals-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.walk :as walk]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.or.lp-certificate-test :as fixtures]
            [rainbow.or.lp-certificate :as lp]))

(defn- unary [n]
  (nth (iterate #(f/app (f/const* 'data/succ []) %) (f/const* 'data/zero [])) n))
(defn- legacy-numerals [surface]
  (walk/postwalk #(if (and (vector? %) (= :nat (first %))) (unary (second %)) %) surface))
(defn- core [env surface]
  (let [result (elaborate/core-expression env surface)]
    (assert (= :elaborated (:status result)) (pr-str result))
    (:term result)))

(deftest instance-numbers-and-indices-are-literals
  (let [spec (lp/certificate-spec 'review/literal-lp fixtures/three-by-three)
        nodes (tree-seq coll? seq spec)]
    (is (some #{[:nat 0]} nodes))
    (is (some #{[:nat 2]} nodes))
    (is (not-any? #{(f/const* 'data/zero []) (f/const* 'data/succ [])} nodes)))
  ;; Encoding size does not grow with the coefficient or denominator magnitude.
  (let [n 100000000000000000000N]
    (is (= [:nat n] (#'lp/numeral n)))
    (is (= (f/app (f/const* 'nnrat/make []) [:nat 3] [:nat (dec n)])
           (#'lp/nnrat-literal 3 n)))))

(deftest literal-and-unary-certificates-prove-the-same-claims
  (let [env @fixtures/base]
    (doseq [instance [fixtures/penalty-mix fixtures/three-by-three]
            make-spec [lp/certificate-spec lp/value-spec]]
      (let [spec (make-spec 'review/literal-lp instance)
            type (core env (:type spec)) proof (core env (:value spec))
            old-type (core env (legacy-numerals (:type spec)))
            old-proof (core env (legacy-numerals (:value spec)))]
        (is (true? (kernel/definitionally-equal? env type old-type)))
        (is (= :checked (:status (kernel/check env proof old-type))))
        (is (= :checked (:status (kernel/check env old-proof type))))))
    (let [result (lp/certify env fixtures/three-by-three)]
      (is (= :certified (:status result)))
      (doseq [[_ {:keys [id]}] (:declarations result)]
        (is (= #{} (kernel/axioms (:environment result) id)))
        (is (some #(and (vector? %) (= :nat (first %)))
                  (tree-seq coll? seq (:rainbow/value (environment/declaration (:environment result) id)))))))))

(deftest surface-literals-are-validated-and-preserve-exact-values
  (let [env @fixtures/base]
    (doseq [n [0 1 100000000000000000000N]]
      (is (= [:nat n] (core env [:nat n])))
      (is (= :checked (:status (kernel/check env (core env [:nat n]) (core env lp/nat))))))
    (doseq [bad [[:nat -1] [:nat 1/2] [:nat 1.0] [:nat] [:nat 1 2]]]
      (is (not= :elaborated (:status (elaborate/core-expression env bad)))))))
