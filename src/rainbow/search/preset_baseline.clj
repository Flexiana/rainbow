(ns rainbow.search.preset-baseline
  "The baseline search options of the native proving stage (frozen data).")

;; search-options: data recorded from an earlier proving run (pure data, not recomputed here)
(def search-options
'{:native-equality-rewrite? true,
 :states 32,
 :native-classical-cases? true,
 :native-reducible-focus? true,
 :local-application-depth 4,
 :native-classical-tautology? true,
 :native-proposition-extensionality? true,
 :local-application-terms 128,
 :native-logic-focus? true,
 :local-application-compositional? true,
 :native-logic-prune? true,
 :wall-ms 3600000,
 :depth 64,
 :native-function-extensionality? true,
 :native-structural-theorem-reuse? true}
  )
