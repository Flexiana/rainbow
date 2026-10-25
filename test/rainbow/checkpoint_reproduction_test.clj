(ns rainbow.checkpoint-reproduction-test
  "A stored checkpoint must be what its milestone rebuilds from source (`lein reproduce`). 1.4.2 broke
  that twice: the migrated checkpoints lacked the kernel's derived :rainbow/level-requirements that a
  rebuild wrote, and a rebuild dropped the :retracted-mappings the migration added. A milestone's
  precommitted input id must also still name its migrated input."
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.persistence :as persistence]))

;; migrated in 1.4.2 (instFiniteProp retracted); holds list/length, which requires u >= 1
(def migrated-checkpoint-path "artifacts/or-contraction/checkpoint.edn.gz")

(def loaded (delay (day54/load-checkpoint migrated-checkpoint-path)))

(deftest a-replayed-checkpoint-rebuilds-to-its-recorded-id
  (let [prior @loaded
        rebuilt (frontier/checkpoint {:prior prior :environment (:environment prior)
                                   :new-mappings [] :evaluations []})]
    (is (= :replayed (:status prior)))
    (is (= ["instFiniteProp"] (mapv :foreign/name (:retracted-mappings prior))))
    (is (= (:retracted-mappings prior) (:retracted-mappings rebuilt)))
    (is (= (:checkpoint/id prior) (:rainbow.checkpoint/id rebuilt)))))

(deftest level-requirements-are-derived-not-stored
  (let [environment (:environment @loaded)
        declarations (vals (:rainbow.environment/declarations environment))
        artifact (persistence/environment-artifact environment)]
    (is (some :rainbow/level-requirements declarations) "the kernel recorded some on replay")
    (is (not-any? :rainbow/level-requirements (:rainbow.artifact/declarations artifact)))
    (is (not-any? (comp :rainbow/level-requirements :entry/value) (:rainbow.artifact/entries artifact)))))

(deftest a-precommitted-input-id-follows-the-recorded-migration
  (let [record (edn/read-string (slurp (first day54/checkpoint-migrations-paths)))
        [before after] (first (:migration/checkpoint-ids record))
        [other _] (second (:migration/checkpoint-ids record))]
    (is (= 249 (count (:migration/checkpoint-ids record))))
    (is (day54/same-input-checkpoint? after after))
    (is (day54/same-input-checkpoint? before after))
    (is (not (day54/same-input-checkpoint? after before)) "a migration is not undone")
    (is (not (day54/same-input-checkpoint? other after)))
    (is (not (day54/same-input-checkpoint? nil after)))
    ;; vector-equivalence-laws: rewritten in 1.4.2, rerun from source in 1.4.3
    (is (day54/same-input-checkpoint? "sha256:62a17c10b9119f7ace0d2f06e2b79a0236b59b3a5a8d531516f696313eb483ad"
                                      "sha256:913020e32023c621869090c17fcdc7b562870fb00f889206c15062ab7d79cbd1"))))
