(ns rainbow.repl
  "REPL-first operations over the same immutable proof functions used by search."
  (:refer-clojure :exclude [type])
  (:require [clojure.set :as set]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.search :as search]
            [rainbow.session :as session]
            [rainbow.tactic :as tactic]))

(defn goal
  ([environment target] (proof/start environment target))
  ([environment target options] (proof/start environment target options)))

(defn surface-goal
  ([environment surface] (surface-goal environment surface {}))
  ([environment surface options]
   (let [elaborated (elaborate/type-expression surface)]
     (if (= :elaborated (:status elaborated))
       (proof/start environment (:term elaborated) options)
       elaborated))))

(defn goals [state] (:proof/goals state))
(defn context [state] (:goal/context (proof/current-goal state)))
(defn proof-state [result-or-state] (or (:state result-or-state) result-or-state))
(defn try! [state tactic] (tactic/run state tactic))
(defn search! [state budget] (search/prove state budget))
(defn why [result] (:failure result))
(defn checkpoint [state label] (session/checkpoint state label))
(defn restore [checkpoint] (session/restore checkpoint))

(defn diff-attempts [left right]
  {:only-left (set/difference (:proof/attempted left) (:proof/attempted right))
   :only-right (set/difference (:proof/attempted right) (:proof/attempted left))})

(defn- compile-step [step]
  (case (first step)
    :intro (tactic/intro (second step))
    :exact (tactic/exact (second step))
    :apply (tactic/apply (second step))
    :assumption (tactic/assumption)
    :refine (tactic/refine (second step) (nth step 2))
    :rewrite (tactic/rewrite (second step) (or (nth step 2 nil) {}))
    :simplify (tactic/simplify (or (second step) []) (or (nth step 2 nil) {}))
    :calc (tactic/calc (second step))
    :induction (tactic/induction (second step))
    (throw (ex-info "Unsupported tactic program step"
                    {:error/category :repl/unsupported-step :step step}))))

(defn run-program [started steps]
  (loop [result started
         remaining steps]
    (if-let [step (first remaining)]
      (if (contains? #{:ready :progress} (:status result))
        (if (= :search (first step))
          (recur (search/prove (:state result) (or (second step) {})) (next remaining))
          (recur (tactic/run (:state result) (compile-step step)) (next remaining)))
        result)
      result)))

(defn declare-theorem
  "Elaborates quoted surface data and interprets a quoted proof program without host evaluation."
  [environment alias options surface proof-form]
  (let [elaborated (elaborate/type-expression surface)]
    (if-not (= :elaborated (:status elaborated))
      elaborated
      (let [target (:term elaborated)
            universes (vec (:universes options))
            proof-result
            (case (first proof-form)
              :core (let [checked (kernel/check environment (second proof-form)
                                                target (set universes))]
                      (if (= :checked (:status checked))
                        {:status :proved
                         :proof {:proof/term (second proof-form)
                                 :proof/type target}
                         :kernel checked}
                        checked))
              :by (run-program (proof/start environment target {:universes universes})
                               (second proof-form))
              {:status :rejected
               :error {:error/category :repl/unsupported-proof-form
                       :proof-form proof-form}})]
        (if-not (= :proved (:status proof-result))
          proof-result
          (kernel/add-declaration
           environment
           {:rainbow/kind :theorem
            :rainbow/aliases #{alias}
            :rainbow/universes universes
            :rainbow/type target
            :rainbow/value (get-in proof-result [:proof :proof/term])
            :rainbow/transparency :opaque
            :rainbow/dependencies #{}
            :rainbow/provenance {:origin :native :producer :repl-tactic-program}
            :rainbow/schema-version 1}))))))
