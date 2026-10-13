(ns rainbow.search.preset-late
  "Catalog, curriculum and checkpoint paths of the late corpus stage (frozen data).")

;; checkpoint-path: data recorded from an earlier proving run (pure data, not recomputed here)
(def checkpoint-path
"artifacts/day86/checkpoint.edn.gz"
  )

;; default-catalog-path: data recorded from an earlier proving run (pure data, not recomputed here)
(def default-catalog-path
"/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz"
  )

;; default-curriculum-path: data recorded from an earlier proving run (pure data, not recomputed here)
(def default-curriculum-path
"artifacts/or40/curriculum.edn"
  )
