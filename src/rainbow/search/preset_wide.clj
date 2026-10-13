(ns rainbow.search.preset-wide
  "The wide candidate search options of the reuse stage, with that stage's catalog and checkpoint paths (frozen data).")

;; candidate-options: data recorded from an earlier proving run (pure data, not recomputed here)
(def candidate-options
'{:native-equality-rewrite? true,
 :states 32,
 :related-reuse-limit 18,
 :native-finite-cover-reuse? true,
 :native-list-cover-witnesses? true,
 :native-classical-cases? true,
 :native-reducible-focus? true,
 :native-finite-witnesses? true,
 :local-application-depth 4,
 :native-classical-tautology? true,
 :native-proposition-extensionality? true,
 :local-application-terms 128,
 :native-logic-focus? true,
 :local-application-compositional? true,
 :native-dependent-theorem-specialization? true,
 :native-logic-prune? true,
 :wall-ms 3600000,
 :native-bool-cases? true,
 :depth 64,
 :native-inductive-cases? true,
 :native-premise-theorem-reuse? true,
 :native-function-extensionality? true,
 :native-structural-theorem-reuse? true,
 :native-focused-intro? true}
  )

;; default-catalog-path: data recorded from an earlier proving run (pure data, not recomputed here)
(def default-catalog-path
'"/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz"
  )

;; checkpoint-path: data recorded from an earlier proving run (pure data, not recomputed here)
(def checkpoint-path
'"artifacts/day74/checkpoint.edn.gz"
  )
