(ns rainbow.profile-principle-identity-test
  "Claim integrity (A2 and A5): a logical
  principle is recognised by the exact id of its declaration, not by a provenance tag or an
  alias, and a name the environment does not have is never classified as constructive."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.profile :as profile]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def base (delay (proposition/build-environment)))

(defn- add! [environment kind alias surface-type surface-value provenance]
  (let [type (:term (elaborate/core-expression environment surface-type))
        value (when surface-value (:term (elaborate/core-expression environment surface-value)))
        result (kernel/add-declaration
                environment
                {:rainbow/kind kind
                 :rainbow/aliases #{alias}
                 :rainbow/universes []
                 :rainbow/type type
                 :rainbow/value value
                 :rainbow/transparency :opaque
                 :rainbow/dependencies (into (term/constants type) (when value (term/constants value)))
                 :rainbow/provenance provenance
                 :rainbow/schema-version 1})]
    (assert (= :accepted (:status result)) (pr-str result))
    [(:environment result) (get-in result [:declaration :rainbow/id])]))

;; every proposition holds: inconsistent, and not excluded middle
(def everything (proposition/forall [['claim 'Prop]] 'claim))

(defn- uses [environment axiom-alias]
  ;; a theorem whose closure is exactly the given axiom
  (add! environment :theorem 'test/uses-it (proposition/truth)
        (proposition/app (proposition/const* axiom-alias []) (proposition/truth))
        {:origin :native :producer :test}))

(deftest a-provenance-tag-does-not-make-an-axiom-a-principle
  (let [[env axiom] (add! @base :axiom 'test/anything everything nil
                          {:origin :native :producer :explicit-logical-profile
                           :logical/profile :classical :logical/principle :classical})
        [env id] (uses env 'test/anything)
        c (profile/classify-declaration env id)]
    (is (= :unknown (profile/principle-of env axiom)))
    (is (= #{axiom} (:logical/unknown-axiom-ids c)))
    (is (= :unknown (:logical/profile c)))
    (is (false? (profile/within-profile? c :classical)))))

(deftest an-alias-does-not-make-an-axiom-a-principle
  (let [[env axiom] (add! @base :axiom 'logic/excluded-middle everything nil {:origin :native :producer :test})
        [env id] (uses env 'logic/excluded-middle)
        c (profile/classify-declaration env id)]
    (is (= :unknown (profile/principle-of env axiom)))
    (is (= :unknown (:logical/profile c)))
    (is (false? (profile/within-profile? c :classical)))))

(deftest the-declared-principles-are-still-recognised
  (doseq [p [:classical :proof-irrelevant :mathlib-complete-logic]]
    (testing p
      (let [{:keys [environment] :as activation} (profile/activate @base p)]
        (doseq [d (:logical/declarations activation)]
          (is (= (get-in d [:rainbow/provenance :logical/principle])
                 (profile/principle-of environment (:rainbow/id d)))
              (str (:rainbow/aliases d))))))))

(deftest a-name-the-environment-does-not-have-is-not-constructive
  (doseq [missing ['test/no-such-theorem "sha256:0000000000000000000000000000000000000000000000000000000000000000"]]
    (let [c (profile/classify-declaration @base missing)]
      (is (false? (:logical/constructive? c)) (str missing))
      (is (= :unknown (:logical/profile c)) (str missing))
      (is (= missing (:logical/unknown-declaration c)))
      (is (false? (profile/within-profile? c :constructive)))
      (is (= #{missing} (:logical/unknown (profile/classify-cohort @base [missing])))))))

(deftest an-alias-of-a-real-declaration-still-classifies
  (let [[env id] (add! @base :theorem 'test/trivially-true (proposition/truth)
                       (proposition/const* 'proposition/trivial []) {:origin :native :producer :test})]
    (is (= :constructive (:logical/profile (profile/classify-declaration env 'test/trivially-true))))
    (is (= :constructive (:logical/profile (profile/classify-declaration env id))))))
