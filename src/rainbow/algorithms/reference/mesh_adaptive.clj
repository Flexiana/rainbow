(ns rainbow.algorithms.reference.mesh-adaptive
  "Executable exact-rational Mesh Adaptive Direct Search (AHoF O39). The poll step
  matches the proved Rainbow definition; `poll-and-adapt` performs one MADS
  iteration: poll the mesh points, accept an improvement, and coarsen or refine
  the mesh size accordingly."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn poll
  "x' = x + delta * direction."
  [x delta direction]
  (vector/add x (vector/scale delta direction)))

(defn poll-and-adapt
  "One MADS iteration on `objective` from incumbent `x` with mesh size `delta`
  over poll `directions`. Returns [x' delta']: on a successful poll the mesh
  doubles, otherwise it halves."
  [objective x delta directions]
  (let [candidates (map #(poll x delta %) directions)
        best (apply min-key objective x candidates)]
    (if (< (objective best) (objective x))
      [best (* delta 2)]
      [x (/ delta 2)])))
