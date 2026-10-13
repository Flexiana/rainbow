(ns rainbow.applied-higher-order-functions-curriculum-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.canonical :as canonical]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]))

(deftest catalog-parser-preserves-identity-category-and-patterns
  (let [text (str "### Example Algorithms\n\n"
                  "| # | Algorithm | Primary HOF | Secondary HOFs | Note |\n"
                  "|---|---|---|---|---|\n"
                  "| O1 | Example | ITERATE + DELEGATE | MAP-OVER | note |\n")]
    (is (= [{:ahof/id "O1"
             :ahof/domain :optimization
             :ahof/name "Example"
             :ahof/category "Example Algorithms"
             :ahof/patterns [:iterate :delegate :map-over]
             :ahof/source-file "catalog/example.md"
             :ahof/outcome :pending
             :ahof/pending-reason :not-yet-audited
             :ahof/evidence []}]
           (ahof/parse-catalog-text
            :optimization "catalog/example.md" text)))))

(deftest recorded-ledger-is-complete-distinct-and-content-addressed
  (let [{:keys [status ledger]} (ahof/load-ledger ahof/ledger-path)
        algorithms (:ahof-ledger/algorithms ledger)
        ids (map :ahof/id algorithms)]
    (is (= :replayed status))
    (is (= (:ahof-ledger/id ledger)
           (canonical/content-id (dissoc ledger :ahof-ledger/id))))
    (is (= 222 (count algorithms) (count (distinct ids))))
    (is (= {:optimization 75 :decision-making 83 :validation 64}
           (frequencies (map :ahof/domain algorithms))))
    (is (= #{"O1" "O75" "D1" "D83" "V1" "V64"}
           (set (filter #{"O1" "O75" "D1" "D83" "V1" "V64"} ids))))
    (is (= {:pending 0 :proved 222 :bug 0}
           (get-in ledger [:ahof-ledger/summary :outcomes])))
    (is (= {:total 5 :outcomes {:proved 5}}
           (get-in ledger [:ahof-ledger/summary :credited-results])))
    (is (= ["decision-guarantee-audit-v0"
            "kochenderfer-gauss-seidel" "kochenderfer-lqr"
            "kochenderfer-nnls" "kochenderfer-stieltjes"]
           (mapv :ahof/id (:ahof-ledger/credited-results ledger))))
    (is (= [
            "O1" "O2" "O3" "O4" "O5" "O6" "O7" "O8" "O9" "O10" "O11" "O12"
            "O13" "O14" "O15" "O16" "O17" "O18" "O19" "O20" "O21" "O22" "O23"
            "O24" "O25" "O26" "O27" "O28" "O29" "O30" "O31" "O32" "O33" "O34"
            "O35" "O36" "O37" "O38" "O39" "O40" "O41" "O42" "O43" "O44" "O45"
            "O46" "O47" "O48" "O49" "O50" "O51" "O52" "O53" "O54" "O55" "O56"
            "O57" "O58" "O59" "O60" "O61" "O62" "O63" "O64" "O65" "O66" "O67"
            "O68" "O69" "O70" "O71" "O72" "O73" "O74" "O75" "D1" "D2" "D3"
            "D4" "D5" "D6" "D7" "D8" "D9" "D10" "D11" "D12" "D13" "D14" "D15"
            "D16" "D17" "D18" "D19" "D20" "D21" "D22" "D23" "D24" "D25" "D26"
            "D27" "D28" "D29" "D30" "D31" "D32" "D33" "D34" "D35" "D36" "D37"
            "D38" "D39" "D40" "D41" "D42" "D43" "D44" "D45" "D46" "D47" "D48"
            "D49" "D50" "D51" "D52" "D53" "D54" "D55" "D56" "D57" "D58" "D59"
            "D60" "D61" "D62" "D63" "D64" "D65" "D66" "D67" "D68" "D69" "D70"
            "D71" "D72" "D73" "D74" "D75" "D76" "D77" "D78" "D79" "D80" "D81"
            "D82" "D83" "V1" "V2" "V3" "V4" "V5" "V6" "V7" "V8" "V9" "V10"
            "V11" "V12" "V13" "V14" "V15" "V16" "V17" "V18" "V19" "V20" "V21"
            "V22" "V23" "V24" "V25" "V26" "V27" "V28" "V29" "V30" "V31" "V32"
            "V33" "V34" "V35" "V36" "V37" "V38" "V39" "V40" "V41" "V42" "V43"
            "V44" "V45" "V46" "V47" "V48" "V49" "V50" "V51" "V52" "V53" "V54"
            "V55" "V56" "V57" "V58" "V59" "V60" "V61" "V62" "V63" "V64"
]
           (mapv :ahof/id (filter #(= :proved (:ahof/outcome %))
                                  algorithms))))
    (is (= 0 (count (filter #(= :pending (:ahof/outcome %))
                              algorithms))))
    (is (every? seq (map :content-sha256
                         (get-in ledger
                                 [:ahof-ledger/source :catalog-files]))))))

(deftest proof-and-bug-evidence-boundaries-are-explicit
  (let [acceptance
        (get-in (-> (ahof/load-ledger ahof/ledger-path) :ledger)
                [:ahof-ledger/acceptance])]
    (is (= #{:proved :bug} (:terminal-outcomes acceptance)))
    (is (some #{:kernel-checked-proof} (:proof-requires acceptance)))
    (is (some #{:minimal-reproduction} (:bug-requires acceptance)))
    (is (= [:mathematical-theorem :rainbow-evaluation
            :clojure-correspondence :output-satisfies-theorem]
           (:executable-claim-boundaries acceptance)))))
