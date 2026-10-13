(ns rainbow.algorithms.reference.failure-probability-monitor
  "Executable exact-rational failure-probability monitor: the system is safe while
  the failure-probability estimate stays at or below the risk threshold, and the
  alarm is the complement of that safety test. Matches the proved Rainbow
  definitions.")

(defn safe?
  "True while the failure-probability estimate p is at or below the threshold tau."
  [p tau]
  (<= p tau))

(defn alarm?
  "The alarm is the boolean complement of the safety test."
  [p tau]
  (not (safe? p tau)))
