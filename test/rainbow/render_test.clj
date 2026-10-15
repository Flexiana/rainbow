(ns rainbow.render-test
  "The statement renderer is a view: names from the source spec only when its
  elaboration is exactly the kernel's type, explicit elision, and a legend for every
  notation it uses."
  (:require [clojure.string :as string]
            [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.main :as main]
            [rainbow.math.rational.signed.lp-duality-on :as lp]
            [rainbow.render :as render]))

(def ^:private env
  (delay (lp/extend-environment (:environment (checkpoint/load-checkpoint main/default-checkpoint)))))

(deftest the-lp-certificate-reads-like-a-signature
  (let [{:keys [text names legend elided]} (render/statement @env 'optimization/signed-lp-optimality-certificate-on)]
    (is (= :source names))
    (is (zero? elided))
    (is (string/includes? text "(primal-feasible : ∀ i ∈ rows, Σ j∈cols, M i j · x j ≤ b i)"))
    (is (string/includes? text "(gap : Σ i∈rows, b i · y i = Σ j∈cols, c j · x j)"))
    (is (string/includes? text "→ Σ j∈cols, c j · candidate j ≤ Σ j∈cols, c j · x j"))
    (is (<= (count (string/split-lines text)) 14))
    (is (= "signed/at-most" (get legend "≤")))
    (is (string/includes? (get legend "=") "signed/equivalent"))))

(deftest names-are-generated-when-no-spec-matches
  (let [id (environment/resolve-id @env 'optimization/signed-lp-optimality-certificate-on)
        decl (environment/declaration @env id)
        {:keys [names text]} (render/declaration-statement @env decl 'not/a-loaded-spec)]
    (is (= :generated names))
    (is (string/includes? text "x₁"))))

(deftest elision-is-explicit
  (let [{:keys [text elided]} (render/statement @env 'optimization/signed-lp-optimality-certificate-on {:max-depth 2})]
    (is (pos? elided))
    (is (string/includes? text "…⟨"))))
