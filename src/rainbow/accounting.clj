(ns rainbow.accounting
  "Semantic accounting for learning claims.

  V1.1 requires that reports keep foreign declarations, distinct normalized
  statements, native abstractions, and distinct proof objects SEPARATE, so that
  aliases and coincident statements never inflate a learning claim.

  The four axes really are independent. One declaration can be reachable under
  several aliases, so counting aliases over-reports proof objects. Two different
  proofs can inhabit the same statement once both types are normalized, so
  counting proof objects over-reports statements proved. And a declaration
  mapped to a foreign name is evidence about coverage of someone else's library,
  while one without is a native abstraction Rainbow built for itself -- summing
  them is not a meaningful total of anything.

  `account` therefore reports each axis separately and additionally names where
  a naive count would have collapsed, so the over-reporting is visible rather
  than merely avoided."
  (:require [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.profile :as profile]))

(def schema-version 1)

(defn- reject! [category message data]
  (throw (ex-info message (assoc data :error/category category))))

(defn- normal-form [checked-environment type]
  (let [result (kernel/normalize checked-environment type)]
    (when-not (= :normalized (:status result))
      (reject! :accounting/normalization-failed
               "Declaration type did not normalize for accounting"
               {:result result}))
    (:term result)))

(defn- statement-key [checked-environment declaration]
  (canonical/content-id
   {:universes (:rainbow/universes declaration)
    :statement (normal-form checked-environment (:rainbow/type declaration))}))

(defn- foreign-name [declaration]
  (get-in declaration [:rainbow/provenance :foreign/name]))

(defn- resolve! [checked-environment id-or-alias]
  (let [declaration (environment/declaration checked-environment id-or-alias)]
    (when-not declaration
      (reject! :accounting/unknown-declaration
               "Cannot account for a declaration that is not in the environment"
               {:id id-or-alias}))
    declaration))

(defn account
  "Counts a cohort of declarations along four independent axes.

  `:accounting/declarations` is how many ids were asked about -- the number that
  naively inflates. The other three are the honest ones:

    :accounting/proof-objects        distinct semantic declaration ids, so a
                                     declaration carrying several aliases counts
                                     once;
    :accounting/statements           distinct normalized types, so two proofs of
                                     the same statement count as one statement;
    :accounting/foreign-declarations declarations mapped to a foreign name;
    :accounting/native-abstractions  declarations with no foreign name -- the
                                     library Rainbow built for itself.

  `:accounting/coincident` names the statement groups that collapsed and
  `:accounting/aliased` the declarations reachable under more than one alias, so
  a reader can see exactly where a naive count would have over-reported.

  Requesting a logical profile additionally reports the cohort's classification,
  since a proof that rests on an axiom is not the same asset as one that does
  not."
  ([checked-environment ids] (account checked-environment ids nil))
  ([checked-environment ids requested-profile]
   (let [entries
         (mapv (fn [id-or-alias]
                 (let [declaration (resolve! checked-environment id-or-alias)]
                   {:id (:rainbow/id declaration)
                    :aliases (set (:rainbow/aliases declaration))
                    :foreign/name (foreign-name declaration)
                    :statement (statement-key checked-environment declaration)}))
               ids)
         by-statement (group-by :statement entries)
         proof-objects (into (sorted-set) (map :id) entries)
         foreign (filterv :foreign/name entries)
         coincident
         (into (sorted-map)
               (keep (fn [[statement group]]
                       (let [distinct-proofs (into (sorted-set)
                                                   (map :id) group)]
                         (when (< 1 (count distinct-proofs))
                           [statement (vec distinct-proofs)]))))
               by-statement)
         aliased
         (into (sorted-map)
               (keep (fn [{:keys [id aliases]}]
                       (when (< 1 (count aliases))
                         [id (vec (sort (map str aliases)))]))
                     entries))]
     (cond-> {:accounting/schema-version schema-version
              :accounting/declarations (count entries)
              :accounting/proof-objects (count proof-objects)
              :accounting/statements (count by-statement)
              :accounting/foreign-declarations (count foreign)
              :accounting/native-abstractions (- (count entries) (count foreign))
              :accounting/coincident coincident
              :accounting/aliased aliased}
       requested-profile
       (assoc :accounting/logical
              (profile/classify-cohort checked-environment
                                       (vec proof-objects)
                                       requested-profile))))))

;; ---- foreign-mapping cohorts -----------------------------------------------

(defn- mapping-proof-id [mapping]
  (or (:proof/id mapping) (:native/id mapping)))

(defn mapping-account
  "The published `:proofs` counts for a cohort of foreign mappings.

  Every day report answers the same four questions and, before this, each
  answered them with its own inline expression -- five different spellings
  across thirty-nine files. They are unified here.

  NEW semantic proof objects is deliberately not just the number of distinct
  proof ids in the mappings. A mapping onto a declaration that ALREADY existed
  reuses a native abstraction and creates nothing new, and a stroke can create a
  new proof object that is not a mapping at all, such as an invented lemma. Both
  cases are real -- day 37 maps `Iff.iff` onto an existing declaration and
  correctly publishes zero, day 42 publishes three for two mappings plus one
  invented lemma -- so the count takes them as inputs:

    new = (distinct mapping proof ids MINUS reused) PLUS additional."
  ([mappings] (mapping-account mappings nil))
  ([mappings {:keys [reused additional]}]
   (let [ids (into #{} (keep mapping-proof-id) mappings)
         reused (set reused)
         additional (set additional)
         fresh (into (into #{} (remove reused) ids) additional)]
     {:accounting/schema-version schema-version
      :accounting/foreign-mappings (count mappings)
      :accounting/distinct-proof-objects (count ids)
      :accounting/native-abstractions-reused (count (filter reused ids))
      :accounting/new-semantic-proof-objects (count fresh)
      :accounting/axiom-profiles (frequencies (map :axioms mappings))})))

(defn new-proof-objects
  "The `:new-semantic-proof-objects` count for a mapping cohort."
  ([mappings] (new-proof-objects mappings nil))
  ([mappings options]
   (:accounting/new-semantic-proof-objects (mapping-account mappings options))))

(defn inflated?
  "True when a naive declaration count would over-report the cohort, because
  aliases or coincident statements collapse under semantic identity."
  [accounting]
  (or (not= (:accounting/declarations accounting)
            (:accounting/proof-objects accounting))
      (not= (:accounting/proof-objects accounting)
            (:accounting/statements accounting))))
