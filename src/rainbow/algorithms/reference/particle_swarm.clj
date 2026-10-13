(ns rainbow.algorithms.reference.particle-swarm
  "Executable exact-rational Particle Swarm Optimization (AHoF O45). The
  per-particle velocity and position update matches the proved Rainbow
  definitions; the global-best selection (the REDUCE the proved core leaves as
  an executable concern) is included here over exact rational fitness values."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn velocity-update
  "v' = w*v + c1*(pbest - x) + c2*(gbest - x)."
  [w c1 c2 velocity position pbest gbest]
  (vector/add
   (vector/scale w velocity)
   (vector/add
    (vector/scale c1 (vector/subtract pbest position))
    (vector/scale c2 (vector/subtract gbest position)))))

(defn position-update
  "x' = x + v'."
  [position velocity]
  (vector/add position velocity))

(defn step
  "One full particle update: recompute the velocity, then move by it. Returns
  the pair [position' velocity']."
  [w c1 c2 velocity position pbest gbest]
  (let [velocity' (velocity-update w c1 c2 velocity position pbest gbest)]
    [(position-update position velocity') velocity']))

(defn global-best
  "The REDUCE over the swarm: the position minimizing an exact-rational
  objective (ties broken by first occurrence)."
  [objective positions]
  (reduce (fn [best candidate]
            (if (< (objective candidate) (objective best)) candidate best))
          (first positions)
          (rest positions)))
