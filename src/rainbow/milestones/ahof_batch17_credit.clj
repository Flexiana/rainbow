(ns rainbow.milestones.ahof-batch17-credit
  "Seventeenth batch: ten fresh native proofs -- V12 V32 V46 V52 V56 V62 V42 V2 V53 V31."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.falsification-opt :as fo]
            [rainbow.algorithms.proofs.ahof.multilevel-splitting :as ms]
            [rainbow.algorithms.proofs.ahof.partitioning :as pt]
            [rainbow.algorithms.proofs.ahof.state-abstraction :as sa]
            [rainbow.algorithms.proofs.ahof.surrogate-explanation :as se]
            [rainbow.algorithms.proofs.ahof.mc-dropout :as md]
            [rainbow.algorithms.proofs.ahof.mean-value-inclusion :as mv]
            [rainbow.algorithms.proofs.ahof.bayesian-param :as bp]
            [rainbow.algorithms.proofs.ahof.policy-visualization :as pv]
            [rainbow.algorithms.proofs.ahof.ratio-normalizing :as rn]))

(def AT [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
         {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the certificate"}])
(def IF [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
         {:target/name 'logic/if-data :statement "eliminator is present"}])
(def MUL [{:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}
          {:target/name 'nnrat/equivalent :statement "exact-rational equivalence is present"}])
(def DIV [{:target/name 'nnrat/divide :statement "exact-rational division is present"}
          {:target/name 'nnrat/equivalent :statement "exact-rational equivalence is present"}])
(defn- m [e d t] [{:extend e :defs d :thms t}])

(def configs
  [{:id "V12" :name "Falsification as Optimization" :source-file "catalog/03_validation_algorithms.md"
    :listing "Cast falsification as minimizing STL robustness; a violation is found when robustness drops to or below the margin."
    :kind :ahof-v12-falsification-opt :dir "artifacts/ahof/v12-falsification-opt"
    :modules (m fo/extend-environment fo/definition-ids fo/theorem-ids) :baseline-prereqs AT
    :package 'fals-opt/low-robustness-violation
    :claim-boundaries {:exact-rational-only true :robustness-violation-decision :proved :global-optimizer :not-claimed}
    :spec {:module 'fals-opt :headline 'fals-opt/violation-found?}}
   {:id "V32" :name "Multilevel Splitting" :source-file "catalog/03_validation_algorithms.md"
    :listing "Estimate rare-event probability by splitting particles that cross intermediate levels; a particle reaches a level when its score meets it."
    :kind :ahof-v32-multilevel-splitting :dir "artifacts/ahof/v32-multilevel-splitting"
    :modules (m ms/extend-environment ms/definition-ids ms/theorem-ids) :baseline-prereqs AT
    :package 'multilevel/crosses-level
    :claim-boundaries {:exact-rational-only true :level-crossing-decision :proved :splitting-schedule :not-claimed}
    :spec {:module 'multilevel :headline 'multilevel/reaches-level?}}
   {:id "V46" :name "Partitioning" :source-file "catalog/03_validation_algorithms.md"
    :listing "Recursively split the set into cells small enough for accurate local over-approximation; a cell is fine when its diameter is within tolerance."
    :kind :ahof-v46-partitioning :dir "artifacts/ahof/v46-partitioning"
    :modules (m pt/extend-environment pt/definition-ids pt/theorem-ids) :baseline-prereqs AT
    :package 'partitioning/small-cell-fine
    :claim-boundaries {:exact-rational-only true :diameter-tolerance-decision :proved :split-heuristic :not-claimed}
    :spec {:module 'partitioning :headline 'partitioning/fine-enough?}}
   {:id "V52" :name "Discrete State Abstraction" :source-file "catalog/03_validation_algorithms.md"
    :listing "Map concrete states to abstract cells; two states share a cell when their distance is within the cell radius."
    :kind :ahof-v52-state-abstraction :dir "artifacts/ahof/v52-state-abstraction"
    :modules (m sa/extend-environment sa/definition-ids sa/theorem-ids) :baseline-prereqs AT
    :package 'abstraction/within-cell-same
    :claim-boundaries {:exact-rational-only true :cell-membership-decision :proved :abstraction-refinement :not-claimed}
    :spec {:module 'abstraction :headline 'abstraction/same-cell?}}
   {:id "V56" :name "Surrogate Model Explanation" :source-file "catalog/03_validation_algorithms.md"
    :listing "Fit an interpretable surrogate to a black-box model; the explanation is faithful when the surrogate's local fidelity error is within tolerance."
    :kind :ahof-v56-surrogate-explanation :dir "artifacts/ahof/v56-surrogate-explanation"
    :modules (m se/extend-environment se/definition-ids se/theorem-ids) :baseline-prereqs AT
    :package 'surrogate-exp/low-error-faithful
    :claim-boundaries {:exact-rational-only true :fidelity-error-decision :proved :surrogate-fitting :not-claimed}
    :spec {:module 'surrogate-exp :headline 'surrogate-exp/faithful?}}
   {:id "V62" :name "MC Dropout Uncertainty" :source-file "catalog/03_validation_algorithms.md"
    :listing "Estimate predictive uncertainty from the variance of dropout forward passes; flag an input uncertain when that variance reaches the threshold."
    :kind :ahof-v62-mc-dropout :dir "artifacts/ahof/v62-mc-dropout"
    :modules (m md/extend-environment md/definition-ids md/theorem-ids) :baseline-prereqs AT
    :package 'mc-dropout/high-variance-uncertain
    :claim-boundaries {:exact-rational-only true :variance-threshold-decision :proved :dropout-sampling :not-claimed}
    :spec {:module 'mc-dropout :headline 'mc-dropout/uncertain?}}
   {:id "V42" :name "Mean-Value Inclusion" :source-file "catalog/03_validation_algorithms.md"
    :listing "A tighter interval extension via the mean-value form; a value is certified within the enclosure when it lies between the bounds."
    :kind :ahof-v42-mean-value-inclusion :dir "artifacts/ahof/v42-mean-value-inclusion"
    :modules (m mv/extend-environment mv/definition-ids mv/theorem-ids) :baseline-prereqs IF
    :package 'mean-value/value-enclosed
    :claim-boundaries {:exact-rational-only true :enclosure-membership :proved :derivative-bound :not-claimed}
    :spec {:module 'mean-value :headline 'mean-value/encloses?}}
   {:id "V2" :name "Bayesian Parameter Learning" :source-file "catalog/03_validation_algorithms.md"
    :listing "Infer model parameters by posterior proportional to likelihood times prior."
    :kind :ahof-v2-bayesian-param :dir "artifacts/ahof/v2-bayesian-param"
    :modules (m bp/extend-environment bp/definition-ids bp/theorem-ids) :baseline-prereqs MUL
    :package 'bayes-param/bayesian-param
    :claim-boundaries {:exact-rational-only true :posterior-score-product :proved :conjugate-update :not-claimed}
    :spec {:module 'bayes-param :headline 'bayes-param/posterior-score}}
   {:id "V53" :name "Policy Visualization" :source-file "catalog/03_validation_algorithms.md"
    :listing "Render a policy by displaying the greedy (maximal-value) action at each state."
    :kind :ahof-v53-policy-visualization :dir "artifacts/ahof/v53-policy-visualization"
    :modules (m pv/extend-environment pv/definition-ids pv/theorem-ids) :baseline-prereqs IF
    :package 'policy-viz/greedy-value-is-maximum
    :claim-boundaries {:exact-rational-only true :greedy-max-selection :proved :rendering :not-claimed}
    :spec {:module 'policy-viz :headline 'policy-viz/greedy-value}}
   {:id "V31" :name "Ratio of Normalizing Constants" :source-file "catalog/03_validation_algorithms.md"
    :listing "Estimate the ratio of two normalizing constants Z1/Z2 (Bayes factors, bridge sampling)."
    :kind :ahof-v31-ratio-normalizing :dir "artifacts/ahof/v31-ratio-normalizing"
    :modules (m rn/extend-environment rn/definition-ids rn/theorem-ids) :baseline-prereqs DIV
    :package 'ratio-nc/unequal-ratio-is-two
    :claim-boundaries {:exact-rational-only true :normalizing-ratio :proved :bridge-estimator :not-claimed}
    :spec {:module 'ratio-nc :headline 'ratio-nc/ratio}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
