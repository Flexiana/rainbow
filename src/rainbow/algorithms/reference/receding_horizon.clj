(ns rainbow.algorithms.reference.receding-horizon
  "Executable Receding Horizon Control / MPC (AHoF D31). The first-action control
  law matches the proved Rainbow definition; `control` runs the closed loop:
  plan over the horizon, apply the first action, advance the state, repeat.")

(defn first-action
  "The applied control: the plan's first action, or the default if empty."
  [default plan]
  (if (seq plan) (first plan) default))

(defn control
  "Run `steps` of receding-horizon control from `state`. `plan-fn` returns the
  finite-horizon action plan from a state; `dynamics` advances the state under an
  action. Returns the sequence of applied actions."
  [plan-fn dynamics default state steps]
  (loop [state state applied [] remaining steps]
    (if (zero? remaining)
      applied
      (let [action (first-action default (plan-fn state))]
        (recur (dynamics state action) (conj applied action) (dec remaining))))))
