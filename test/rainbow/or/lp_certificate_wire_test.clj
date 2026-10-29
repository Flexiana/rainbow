(ns rainbow.or.lp-certificate-wire-test
  (:require [clojure.edn :as edn]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-plan-report-bridge :as plan]
            [rainbow.math.rational.signed.lp-gap-quality-bridge :as quality]
            [rainbow.or.lp-certificate :as lp]
            [rainbow.or.lp-certificate-wire :as wire]
            [rainbow.or.lp-original-plan-verifier :as verifier]
            [rainbow.or.lp-epsilon-verifier-test :as epsilon-test]))

(def ^:private env (delay @(var-get #'epsilon-test/env)))
(def ^:private maximum {:matrix [[1]] :capacities [2] :margins [1] :prices [1] :plan [2]})
(def ^:private actual (#'lp/standard-form maximum))
(def ^:private report {:achieved 2 :bound 2 :gap 0 :direction :upper})
(defn- values [specs] (into {} (map (fn [[k s]] [k (:value s)])) specs))
(def ^:private exact (delay (values (plan/optimality-specs maximum actual report))))
(defn- raw [x] (binding [*print-namespace-maps* false *print-length* nil *print-level* nil] (pr-str x)))
(defn- category [thunk]
  (try (thunk) :unexpected-success (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))
(defn- skeleton []
  ;; Deliberately UNCHECKED dummy evidence: codec acceptance is not verification.
  {:format wire/format-id :claim :feasible-report :request/id (verifier/request-id maximum actual report)
   :proofs (zipmap verifier/report-obligations (repeat (f/const* 'proposition/trivial [])))})

(deftest real-wire-replay-for-every-claim-and-exact-rational-budget
  (doseq [[label original r options status]
          [[:basic maximum report {} :original-plan-report-verified]
           [:exact maximum report {:claim :optimal-plan} :original-plan-optimal]
           [:epsilon (assoc maximum :plan [1]) {:achieved 1 :bound 2 :gap 1 :direction :upper}
            {:claim :epsilon-plan :epsilon 1} :original-plan-epsilon-verified]
           [:fractional (assoc maximum :plan [3/2]) {:achieved 3/2 :bound 2 :gap 1/2 :direction :upper}
            {:claim :epsilon-plan :epsilon 1/2} :original-plan-epsilon-verified]
           [:minimum {:matrix [[-1]] :capacities [-1] :margins [1] :prices [1] :plan [2] :sense :minimize}
            {:achieved 2 :bound 1 :gap 1 :direction :lower}
            {:claim :epsilon-plan :epsilon 1} :original-plan-epsilon-verified]
           [:empty {:matrix [] :capacities [] :margins [] :prices [] :plan []}
            {:achieved 0 :bound 0 :gap 0 :direction :upper}
            {:claim :epsilon-plan :epsilon 0} :original-plan-epsilon-verified]]]
    (let [a (#'lp/standard-form original)
          p (values (case (:claim options)
                      :optimal-plan (plan/optimality-specs original a r)
                      :epsilon-plan (quality/epsilon-specs original a r (:epsilon options))
                      (plan/plan-report-specs original a r)))
          text (wire/encode original a r p options) decoded (wire/decode text) e @env
          result (with-redefs [plan/plan-report-specs (fn [& _] (throw (AssertionError. "Producer called")))
                              quality/epsilon-specs (fn [& _] (throw (AssertionError. "Producer called")))]
                   (wire/replay e original a r text options))]
      (println "LP-WIRE" label (pr-str (#'wire/preflight! text))
               (pr-str (select-keys result [:status :request/id :audit/id :certificate/id])))
      (is (= p (:proofs decoded)))
      (is (= status (:status result)))
      (is (= (:request/id decoded) (:request/id result) (verifier/request-id original a r options)))
      (is (every? #(and (= :checked (:status %)) (= #{} (:axioms %))) (vals (:verdicts result))))
      (is (string? (:certificate/id result)))
      (is (string? (:audit/id result))))))

(deftest deterministic-serialization-and-no-solver-metadata
  (let [p @exact opts {:claim :optimal-plan}
        text (wire/encode maximum actual report p opts)
        backwards (into (array-map) (reverse (seq p)))
        printed (binding [*print-length* 1 *print-level* 1 *print-meta* true *print-namespace-maps* true]
                  (wire/encode (assoc maximum :customer-secret "DO-NOT-TRANSPORT") actual report backwards opts))
        replayed (wire/replay @env maximum actual report text opts)
        direct (verifier/verify @env maximum actual report p opts)]
    (is (= text printed))
    (is (not (str/includes? text "DO-NOT-TRANSPORT")))
    (is (= direct (dissoc replayed :certificate/id)))
    (is (= #{:format :claim :request/id :proofs} (set (keys (wire/decode text)))))
    (is (= :lp-wire/roundtrip
           (category #(wire/encode maximum actual report
                                    (assoc (select-keys p verifier/report-obligations) :achieved-value (symbol "nil"))))))))

(deftest stale-header-and-claim-refused-before-kernel
  (let [text (wire/encode maximum actual report @exact {:claim :optimal-plan})]
    (doseq [[o r opts] [[(assoc maximum :plan [1]) report {:claim :optimal-plan}]
                       [maximum (assoc report :gap 1) {:claim :optimal-plan}]
                       [maximum report {}]]]
      (let [result (with-redefs [kernel/check (fn [& _] (throw (AssertionError. "Header mismatch first")))]
                     (wire/replay nil o actual r text opts))]
        (is (= :refused (:status result)))
        (is (= :lp-wire/request-mismatch (:error/category result))))))
  (let [original (assoc maximum :plan [1]) r {:achieved 1 :bound 2 :gap 1 :direction :upper}
        p (values (quality/epsilon-specs original actual r 1))
        text (wire/encode original actual r p {:claim :epsilon-plan :epsilon 1})
        result (with-redefs [kernel/check (fn [& _] (throw (AssertionError. "Epsilon mismatch first")))]
                 (wire/replay nil original actual r text {:claim :epsilon-plan :epsilon 2}))]
    (is (= :lp-wire/request-mismatch (:error/category result)))))

(deftest recomputing-a-header-does-not-bypass-mathematics
  (let [opts {:claim :optimal-plan} original (assoc maximum :plan [1])
        packet (wire/decode (wire/encode maximum actual report @exact opts))
        forged (assoc packet :request/id (verifier/request-id original actual report opts))
        result (wire/replay @env original actual report (raw forged) opts)]
    (is (= :rejected (:status result)))
    (is (= :submitted-plan-feasible (:failed-obligation result))))
  (let [opts {:claim :optimal-plan}
        p (assoc @exact :optimality (f/const* 'proposition/trivial []))
        text (wire/encode maximum actual report p opts)
        result (wire/replay @env maximum actual report text opts)]
    (is (= :rejected (:status result))) (is (= :optimality (:failed-obligation result)))
    (is (= :kernel/type-mismatch (get-in result [:verdicts :optimality :error/category]))))
  (let [text (wire/encode maximum actual report @exact {:claim :optimal-plan})
        result (wire/replay @env maximum actual report text {:claim :optimal-plan :reductions 1})]
    (is (= :refused (:status result)))
    (is (= :kernel/resource-limit (get-in result [:verdicts (:failed-obligation result) :error/category])))))

(deftest envelope-version-coverage-and-forbidden-metadata
  (let [packet (skeleton)]
    (doseq [bad (concat [(assoc packet :format :rainbow.lp/proof-values-v999)
                        (assoc packet :claim :unknown) (assoc packet :request/id "not-a-digest")
                        (update packet :proofs dissoc :achieved-value)]
                       (map #(assoc packet % {}) [:environment :reductions :targets :status :original]))]
      (is (= :lp-wire/envelope (category #(wire/decode (raw bad))))))
    (is (= packet (wire/decode (str "; #_ ignored comment [ [ [\n" (raw packet)))))
    (let [string-packet (assoc-in packet [:proofs :achieved-value] "#_ [ ] { } ; quoted \"text\"")]
      (is (= string-packet (wire/decode (raw string-packet)))))
    (is (= :lp-wire/value (category #(wire/decode (raw (assoc-in packet [:proofs :achieved-value] 0.5))))))
    (is (= :lp-wire/syntax (category #(wire/decode (str (raw packet) " {}")))))
    (is (= :lp-wire/syntax (category #(wire/decode "{:a 1 :a 2}"))))))

(deftest unsafe-reader-syntax-and-size-limits-stop-before-edn-reader
  (let [{:keys [max-bytes max-depth max-nodes max-token-chars]} wire/limits]
    (doseq [[text expected]
            [["#=(+ 1 2)" :lp-wire/syntax] ["#_ {} {}" :lp-wire/syntax]
             ["#inst \"2026-09-16\"" :lp-wire/syntax] ["^{} {}" :lp-wire/syntax]
             ["'(x)" :lp-wire/syntax] ["[\\a]" :lp-wire/syntax]
             [(apply str (repeat (inc max-depth) "[")) :lp-wire/size]
             [(apply str (repeat (inc max-token-chars) "x")) :lp-wire/size]
             [(str "[" (apply str (repeat max-nodes "0 ")) "]") :lp-wire/size]
             [(apply str (repeat (inc max-bytes) " ")) :lp-wire/size]
             [(apply str (repeat (inc (quot max-bytes 2)) "é")) :lp-wire/size]]]
      (is (= expected
             (with-redefs [edn/read (fn [& _] (throw (AssertionError. "Reader reached before guard")))]
               (category #(wire/decode text))))))))

(deftest malformed-reader-values-and-encoder-depth-refused
  (doseq [text ["" "[}" "[" "\"unterminated" "1/0"]]
    (is (= :lp-wire/syntax (category #(wire/decode text)))))
  (let [p (select-keys @exact verifier/report-obligations)
        nested (nth (iterate vector 0) (+ 2 (:max-depth wire/limits)))]
    (is (= :lp-wire/size (category #(wire/encode maximum actual report (assoc p :achieved-value nested)))))
    (is (= :lp-wire/value (category #(wire/encode maximum actual report (assoc p :achieved-value '(x)))))))
  (is (= :lp-wire/input (category #(wire/decode nil)))))

(deftest shallow-forms-cannot-expand-past-the-elaboration-depth-guard
  (let [n (inc (:max-expansion-depth wire/limits)) packet (skeleton)]
    (doseq [proof [[:fn (vec (repeat n ['x 'Prop])) 'x]
                  [:forall (vec (repeat n ['x 'Prop])) 'Prop]
                  (into [:app 'x] (repeat n 'x))
                  (into [:->] (repeat n 'Prop))]]
      (let [text (raw (assoc-in packet [:proofs :achieved-value] proof))
            result (with-redefs [elaborate/core-expression (fn [& _] (throw (AssertionError. "Elaborator reached")))]
                     (wire/replay nil maximum actual report text))]
        (is (= :refused (:status result)))
        (is (= :lp-wire/size (:error/category result)))))))
