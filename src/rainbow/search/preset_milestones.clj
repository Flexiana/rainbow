(ns rainbow.search.preset-milestones
  "The candidate search options the algorithm milestones start from (frozen data).")

;; candidate-options: data recorded from an earlier proving run (pure data, not recomputed here)
(def candidate-options
'{:native-equality-rewrite? true,
 :states 64,
 :native-classical-cases? true,
 :native-reducible-focus? true,
 :local-application-depth 4,
 :native-classical-tautology? true,
 :native-proposition-extensionality? true,
 :local-application-terms 128,
 :native-logic-focus? true,
 :local-application-compositional? true,
 :native-logic-prune? true,
 :wall-ms 60000,
 :depth 64,
 :native-function-extensionality? true,
 :native-structural-theorem-reuse? true}
  )
