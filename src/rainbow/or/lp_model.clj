(ns rainbow.or.lp-model
  "Derive an LP instance from a named description of the decision.

  `rainbow.or.lp-certificate` proves a statement about THE MATRIX IT IS GIVEN. If
  that matrix does not encode the customer's actual problem, the proof is
  immaculate and irrelevant. That gap -- assurance level R4 -- is the thing
  standing between a kernel-checked certificate and a decision anyone should act
  on, and it is not closed by proving more theorems about matrices.

  What can be closed is the TRANSCRIPTION half of it. Today a caller hands over
  `[[4 5 0 0 0] ...]`, and nobody can audit that: an auditor knows their business
  rules, not their coefficient layout. Here the caller instead declares

    activities  -- what may be chosen, and what each is worth
    resources   -- what is consumed, how much of it exists, and by what

  and the matrix is DERIVED. The derivation is total and mechanical, so the step
  that used to be a person typing numbers becomes a function anyone can re-run.

  BE CLEAR ABOUT WHAT THIS DOES NOT DO. It does not prove the declaration is
  true of the world. No software can. It proves the matrix says what the
  declaration says -- and `explain` renders every coefficient back to the named
  fact it came from, so the remaining human judgement is made against sentences
  about resources and activities rather than against a grid of numbers. That is
  a smaller and far more checkable gap than the one it replaces."
  (:require [clojure.string :as string]
            [rainbow.or.lp-certificate :as certificate]))

(defn- activity-names [{:keys [activities]}] (mapv :name activities))
(defn- resource-names [{:keys [resources]}] (mapv :name resources))

(defn- consumption
  "How much of `resource` one unit of `activity` uses. Undeclared means none --
  stated here rather than left to a nil-punning accident downstream."
  [resource activity-name]
  (get (:consumption resource) activity-name 0))

(defn derive-instance
  "The LP instance this description denotes.

  One row per resource, one column per activity, in declared order. The order is
  part of the derivation and is preserved in `explain`, so a reader never has to
  infer which row is which."
  [{:keys [activities resources plan prices] :as description}]
  (let [names (activity-names description)]
    {:matrix (mapv (fn [resource] (mapv #(consumption resource %) names)) resources)
     :capacities (mapv :capacity resources)
     :margins (mapv :margin activities)
     :plan (mapv #(get plan % 0) names)
     :prices (mapv #(get prices (:name %) 0) resources)}))

(defn explain
  "Every derived number rendered back to the declaration it came from.

  This is the artifact an auditor reads. It is deliberately prose about named
  resources and activities, because that is what a person can be wrong about in
  a way they will notice."
  [{:keys [activities resources] :as description}]
  (let [names (activity-names description)]
    (concat
     (for [a activities]
       (str "activity '" (:name a) "' is worth " (:margin a) " per unit"))
     (for [r resources]
       (str "resource '" (:name r) "' has capacity " (:capacity r)
            ", consumed per unit by "
            (string/join ", "
                         (for [n names]
                           (str n " x" (consumption r n)))))))))

(defn- undeclared-activities
  "Consumption entries naming an activity that does not exist. A typo here would
  otherwise vanish silently into a zero column."
  [{:keys [resources] :as description}]
  (let [known (set (activity-names description))]
    (for [r resources
          n (keys (:consumption r))
          :when (not (known n))]
      {:resource (:name r) :unknown-activity n})))

(defn check-description
  "Structural faults a derivation would otherwise absorb without complaint."
  [{:keys [activities resources plan prices] :as description}]
  (let [known (set (activity-names description))
        stray (undeclared-activities description)]
    (cond-> []
      (empty? activities) (conj {:fault :no-activities})
      (empty? resources) (conj {:fault :no-resources})
      (seq stray) (conj {:fault :consumption-names-unknown-activity :detail (vec stray)})
      (seq (remove known (keys plan)))
      (conj {:fault :plan-names-unknown-activity
             :detail (vec (remove known (keys plan)))})
      (seq (remove (set (resource-names description)) (keys prices)))
      (conj {:fault :price-names-unknown-resource
             :detail (vec (remove (set (resource-names description)) (keys prices)))}))))

(defn bound-described
  "Prove a bound for a DESCRIPTION rather than for a matrix.

  Refuses a malformed description before any kernel work, because a fault there
  -- a consumption entry naming an activity that does not exist, say -- would
  otherwise be absorbed into a zero column and certified as if intended.

  The result carries `:description` and `:explanation` beside the usual
  certificate fields. That is the point: the audit trail then contains the
  business facts the matrix was derived from, so a reader checks sentences about
  resources rather than a grid, and can re-run the derivation themselves."
  ([checked-environment description] (bound-described checked-environment description nil))
  ([checked-environment description options]
   (let [faults (check-description description)]
     (if (seq faults)
       {:status :rejected
        :error/category :lp-model/malformed-description
        :message (str "The description has faults that would silently change the "
                      "derived instance: " (pr-str (mapv :fault faults)))
        :faults faults}
       (let [instance (derive-instance description)
             result (certificate/bound checked-environment instance options)]
         (assoc result
                :description description
                :explanation (vec (explain description))))))))
