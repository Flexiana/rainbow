(ns rainbow.foreign.ingest
  "Bring a checked foreign (Lean/Mathlib) statement into the native language and register a kernel-checked proof of it.
  (Foreign-import bookkeeping.)"
  (:require [rainbow.canonical :as canonical]
            [rainbow.foreign.aliases.prelude :as aliases]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.foreign.mathlib-native :as mathlib-native]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]))

(def constant-aliases aliases/constant-aliases)

(defn nativeize-statement [checked-environment statement aliases]
  (let [result (mathlib-native/nativeize-statement-type
                checked-environment statement {:constant-aliases aliases})]
    (cond-> result
      (= :nativeized (:status result)) (assoc :statement statement))))

(defn proof-id [result]
  (canonical/content-id
   (select-keys (:proof result)
                [:proof/term :proof/type :proof/environment-id])))

(defn add-result
  ([checked-environment evaluation]
   (add-result checked-environment evaluation
               :measured-prelude-study "prelude-"))
  ([checked-environment {:keys [target result]} producer alias-prefix]
  (let [statement (:statement target)
        proof-term (get-in result [:proof :proof/term])
        alias (symbol "mathlib.reproof"
                      (str alias-prefix (subs (proof-id result) 7 23)))
        added
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem :rainbow/aliases #{alias}
          :rainbow/universes (:universes target)
          :rainbow/type (:type target) :rainbow/value proof-term
          :rainbow/transparency :opaque
          :rainbow/dependencies
          (into (term/constants (:type target)) (term/constants proof-term))
          :rainbow/provenance
          {:origin :native :producer producer
           :foreign/system :lean :foreign/library :mathlib
           :foreign/version mathlib/pinned-version
           :foreign/commit mathlib/pinned-commit
           :foreign/module (:foreign/module statement)
           :foreign/name (:foreign/name statement)
           :foreign/type-fingerprint (:foreign/type-fingerprint statement)
           :foreign/proof-hidden? true}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status added))
      (throw (ex-info "Day 45 checked proof could not be registered"
                      {:foreign/name (:foreign/name target) :result added})))
    [(:environment added)
     {:foreign/name (:foreign/name target)
      :native/id (get-in added [:declaration :rainbow/id])
      :proof/id (proof-id result)
      :axioms (get-in result [:proof :proof/axioms])}])))
