(ns rainbow.history.direct-term-corpus
  "The initial direct-term proof corpus. No tactic or elaborator participates."
  (:require [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.term :as term])
  (:gen-class))

(def u [:param 'u])
(def v [:param 'v])
(def w [:param 'w])
(def z [:param 'z])
(def q [:param 'q])

(defn s [level] (term/sort-term level))
(defn b [index] (term/bound index))
(defn app [function argument] (term/application function argument))
(defn pi [domain body] (term/pi-term domain body))
(defn lam [domain body] (term/lambda-term domain body))
(defn pis [domains body] (reduce (fn [result domain] (pi domain result)) body (reverse domains)))
(defn lams [domains body] (reduce (fn [result domain] (lam domain result)) body (reverse domains)))

(def proofs
  [{:name 'logic/polymorphic-identity
    :universes ['u]
    :type (pi (s u) (pi (b 0) (b 1)))
    :value (lam (s u) (lam (b 0) (b 0)))}

   {:name 'logic/constant-function
    :universes ['u 'v]
    :type (pi (s u) (pi (s v) (pi (b 1) (pi (b 1) (b 3)))))
    :value (lam (s u) (lam (s v) (lam (b 1) (lam (b 1) (b 1)))))}

   {:name 'logic/function-application
    :universes ['u 'v]
    :type (pi (s u)
              (pi (s v)
                  (pi (pi (b 1) (b 1))
                      (pi (b 2) (b 2)))))
    :value (lam (s u)
                (lam (s v)
                     (lam (pi (b 1) (b 1))
                          (lam (b 2) (app (b 1) (b 0))))))}

   {:name 'logic/function-composition
    :universes ['u 'v 'w]
    :type (pi (s u)
              (pi (s v)
                  (pi (s w)
                      (pi (pi (b 1) (b 1))
                          (pi (pi (b 3) (b 3))
                              (pi (b 4) (b 3)))))))
    :value (lam (s u)
                (lam (s v)
                     (lam (s w)
                          (lam (pi (b 1) (b 1))
                               (lam (pi (b 3) (b 3))
                                    (lam (b 4)
                                         (app (b 2) (app (b 1) (b 0)))))))))}

   {:name 'logic/flip
    :universes ['u 'v 'w]
    :type (pi (s u)
              (pi (s v)
                  (pi (s w)
                      (pi (pi (b 2) (pi (b 2) (b 2)))
                          (pi (b 2) (pi (b 4) (b 3)))))))
    :value (lam (s u)
                (lam (s v)
                     (lam (s w)
                          (lam (pi (b 2) (pi (b 2) (b 2)))
                               (lam (b 2)
                                    (lam (b 4)
                                         (app (app (b 2) (b 0)) (b 1))))))))}

   {:name 'logic/implication-transitivity
    :universes []
    :type (pi (s term/zero-level)
              (pi (s term/zero-level)
                  (pi (s term/zero-level)
                      (pi (pi (b 2) (b 2))
                          (pi (pi (b 2) (b 2))
                              (pi (b 4) (b 3)))))))
    :value (lam (s term/zero-level)
                (lam (s term/zero-level)
                     (lam (s term/zero-level)
                          (lam (pi (b 2) (b 2))
                               (lam (pi (b 2) (b 2))
                                    (lam (b 4)
                                         (app (b 1) (app (b 2) (b 0)))))))))}

   {:name 'logic/forall-specialization
    :universes ['u]
    :type (pi (s u)
              (pi (pi (b 0) (s term/zero-level))
                  (pi (pi (b 1) (app (b 1) (b 0)))
                      (pi (b 2) (app (b 2) (b 0))))))
    :value (lam (s u)
                (lam (pi (b 0) (s term/zero-level))
                     (lam (pi (b 1) (app (b 1) (b 0)))
                          (lam (b 2) (app (b 1) (b 0))))))}

   {:name 'logic/compose-four-functions
    :universes ['u 'v 'w 'z 'q]
    :type (pis [(s u) (s v) (s w) (s z) (s q)
                (pi (b 1) (b 1))
                (pi (b 3) (b 3))
                (pi (b 5) (b 5))
                (pi (b 7) (b 7))
                (b 8)]
               (b 5))
    :value (lams [(s u) (s v) (s w) (s z) (s q)
                  (pi (b 1) (b 1))
                  (pi (b 3) (b 3))
                  (pi (b 5) (b 5))
                  (pi (b 7) (b 7))
                  (b 8)]
                 (app (b 4)
                      (app (b 3)
                           (app (b 2)
                                (app (b 1) (b 0))))))}])

(defn declaration [{:keys [name universes type value]}]
  {:rainbow/kind :theorem
   :rainbow/aliases #{name}
   :rainbow/universes (vec universes)
   :rainbow/type type
   :rainbow/value value
   :rainbow/transparency :opaque
   :rainbow/dependencies #{}
   :rainbow/provenance {:origin :native :corpus :day-1}
   :rainbow/schema-version 1})

(defn build-environment []
  (reduce
   (fn [current proof]
     (let [result (kernel/add-declaration current (declaration proof))]
       (when-not (= :accepted (:status result))
         (throw (ex-info "Day-1 proof was rejected"
                         {:proof (:name proof) :result result})))
       (:environment result)))
   (environment/empty-environment)
   proofs))

(defn report []
  (let [checked (build-environment)]
    {:status :passed
     :proofs (count proofs)
     :environment-id (environment/environment-id checked)
     :normal-forms-id
     (canonical/content-id
      (mapv (fn [{:keys [name type value]}]
              [name
               (:term (kernel/normalize checked type))
               (:term (kernel/normalize checked value))])
            proofs))
     :axioms (into {} (map (fn [{:keys [name]}]
                             [name (kernel/axioms checked name)])
                           proofs))}))

(defn -main [& [command path]]
  (case command
    "hash" (let [{:keys [environment-id normal-forms-id]} (report)]
             (println (str environment-id "\t" normal-forms-id)))
    "write" (println (pr-str (persistence/save-environment! (build-environment) path)))
    "replay" (let [result (persistence/load-environment path)]
               (println (pr-str (dissoc result :environment)))
               (when-not (= :replayed (:status result))
                 (System/exit 1)))
    (println (pr-str (report)))))
