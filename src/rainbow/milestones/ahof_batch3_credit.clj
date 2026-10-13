(ns rainbow.milestones.ahof-batch3-credit
  "Third batch: pending AHoF optimizer rows whose proofs need vector ops; chains
  finite-vector before each target module."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.math.finite.vector :as fv]
            [rainbow.algorithms.proofs.powell :as m0]
            [rainbow.algorithms.proofs.hooke-jeeves :as m1]
            [rainbow.algorithms.proofs.noisy-descent :as m2]
            [rainbow.algorithms.proofs.differential-evolution :as m3]
            [rainbow.algorithms.proofs.particle-swarm :as m4]
            [rainbow.algorithms.proofs.firefly :as m5]
            [rainbow.algorithms.proofs.cuckoo-search :as m6]
            [rainbow.algorithms.proofs.interior-point :as m7]
            [rainbow.algorithms.proofs.admm :as m8]
            [rainbow.algorithms.proofs.dual-ascent :as m9]
            [rainbow.algorithms.proofs.full-factorial :as m10]
            [rainbow.algorithms.proofs.latin-hypercube :as m11]))

(def configs
  [
   {:id "O33" :name "Powell's Method"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O33 Powell's Method: the conjugate search-direction generated from a"
    :kind :ahof-o33-powell
    :dir "artifacts/ahof/o33-powell"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'powell/net-direction-3d-example
    :spec {:module 'powell :headline 'powell/net-direction-3d-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O34" :name "Hooke-Jeeves"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O34 Hooke-Jeeves pattern search: the exploratory probe and the pattern"
    :kind :ahof-o34-hooke
    :dir "artifacts/ahof/o34-hooke"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'hooke/pattern-move-3d-example
    :spec {:module 'hooke :headline 'hooke/pattern-move-3d-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O38" :name "Noisy Descent"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O38 Noisy Descent: the WRAP pattern that perturbs a base descent step"
    :kind :ahof-o38-noisy
    :dir "artifacts/ahof/o38-noisy"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m2/extend-environment :defs m2/definition-ids :thms m2/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'noisy/wrap-3d-example
    :spec {:module 'noisy :headline 'noisy/wrap-3d-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O44" :name "Differential Evolution"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O44 Differential Evolution: the differential mutation over vector-valued"
    :kind :ahof-o44-evolution
    :dir "artifacts/ahof/o44-evolution"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m3/extend-environment :defs m3/definition-ids :thms m3/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'evolution/unit-mutation-example
    :spec {:module 'evolution :headline 'evolution/unit-mutation-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O45" :name "Particle Swarm"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O45 Particle Swarm Optimization: the per-particle velocity and position"
    :kind :ahof-o45-swarm
    :dir "artifacts/ahof/o45-swarm"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m4/extend-environment :defs m4/definition-ids :thms m4/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'swarm/step-example
    :spec {:module 'swarm :headline 'swarm/step-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O46" :name "Firefly Algorithm"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O46 Firefly Algorithm: the attraction move over vector-valued state. A"
    :kind :ahof-o46-firefly
    :dir "artifacts/ahof/o46-firefly"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m5/extend-environment :defs m5/definition-ids :thms m5/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'firefly/full-attraction-3d-example
    :spec {:module 'firefly :headline 'firefly/full-attraction-3d-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O47" :name "Cuckoo Search"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O47 Cuckoo Search: the Levy-flight step over vector-valued state. A"
    :kind :ahof-o47-cuckoo
    :dir "artifacts/ahof/o47-cuckoo"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m6/extend-environment :defs m6/definition-ids :thms m6/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'cuckoo/scaled-flight-example
    :spec {:module 'cuckoo :headline 'cuckoo/scaled-flight-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O50" :name "Interior Point / Barrier"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O50 Interior Point / Barrier Method: the transform that keeps iterates"
    :kind :ahof-o50-barrier
    :dir "artifacts/ahof/o50-barrier"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m7/extend-environment :defs m7/definition-ids :thms m7/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'barrier/wide-slack-example
    :spec {:module 'barrier :headline 'barrier/wide-slack-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O51" :name "ADMM"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O51 ADMM (Alternating Direction Method of Multipliers): the scaled-form"
    :kind :ahof-o51-admm
    :dir "artifacts/ahof/o51-admm"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m8/extend-environment :defs m8/definition-ids :thms m8/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'admm/residual-3d-example
    :spec {:module 'admm :headline 'admm/residual-3d-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O52" :name "Dual Ascent"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O52 Dual Ascent: the dual-variable ascent step over vector-valued"
    :kind :ahof-o52-dual-ascent
    :dir "artifacts/ahof/o52-dual-ascent"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m9/extend-environment :defs m9/definition-ids :thms m9/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'dual-ascent/unit-step-3d-example
    :spec {:module 'dual-ascent :headline 'dual-ascent/unit-step-3d-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O58" :name "Full Factorial Sampling"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O58 Full Factorial Sampling: the design size is the product of the"
    :kind :ahof-o58-full-factorial
    :dir "artifacts/ahof/o58-full-factorial"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m10/extend-environment :defs m10/definition-ids :thms m10/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'full-factorial/design-size-empty-example
    :spec {:module 'full-factorial :headline 'full-factorial/design-size-empty-example :vector-prereq 'rainbow.math.finite.vector}}
   {:id "O59" :name "Latin Hypercube Sampling"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O59 Latin Hypercube Sampling: a space-filling design that draws exactly"
    :kind :ahof-o59-latin-hypercube
    :dir "artifacts/ahof/o59-latin-hypercube"
    :modules [{:extend fv/extend-environment :defs fv/definition-ids :thms fv/theorem-ids}
              {:extend m11/extend-environment :defs m11/definition-ids :thms m11/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/from-nnrat :statement "signed-rational embedding is present"}]
    :package 'latin-hypercube/total-strata-4x3-example
    :spec {:module 'latin-hypercube :headline 'latin-hypercube/total-strata-4x3-example :vector-prereq 'rainbow.math.finite.vector}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
