(ns rainbow.algorithms.reference.finite-metropolis-hastings
  "Executable exact-rational companion to the checked two-state MH sampler.")

(def states [0 1])
(def target {0 1/3, 1 2/3})

(defn proposal
  "Independence proposal equal to the target distribution."
  [_source destination]
  (get target destination 0))

(defn acceptance
  "The Hastings ratio is one because proposal and target are identical."
  [_source _destination]
  1)

(defn kernel [source destination]
  (* (proposal source destination)
     (acceptance source destination)))

(defn step [mass]
  (into {}
        (map (fn [destination]
               [destination
                (reduce + (map (fn [source]
                                 (* (get mass source 0)
                                    (kernel source destination)))
                               states))])
             states)))

(defn demo []
  (let [uniform {0 1/2, 1 1/2}]
    {:states states
     :target target
     :kernel (into {}
                   (for [source states]
                     [source (into {}
                                   (for [destination states]
                                     [destination
                                      (kernel source destination)]))]))
     :row-totals (into {}
                       (for [source states]
                         [source (reduce + (map #(kernel source %) states))]))
     :balanced-flow-0-1 (* (target 0) (kernel 0 1))
     :balanced-flow-1-0 (* (target 1) (kernel 1 0))
     :one-step-from-uniform (step uniform)}))
