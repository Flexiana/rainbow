(ns rainbow.native-reproof-test
  (:require [clojure.java.shell :as shell]
            [clojure.test :refer :all]
            [rainbow.history.lean-hidden-body-inhabitation :as lean-hidden-body-inhabitation]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def checked-corpus (delay (lean-hidden-body-inhabitation/build)))

(defn java-command [& arguments]
  (apply shell/sh
         (str (System/getProperty "java.home") "/bin/java")
         "-cp" (System/getProperty "java.class.path")
         "clojure.main"
         arguments))

(deftest hidden-claim-jobs-contain-no-foreign-bodies
  (let [claims (lean-hidden-body-inhabitation/hidden-claims)]
    (is (= 8 (count claims)))
    (doseq [claim claims]
      (is (= #{:foreign/name :foreign/id :claim/type :claim/universes}
             (set (keys claim))))
      (is (not (contains? claim :foreign/raw-value)))
      (is (not (contains? claim :claim/value))))))

(deftest ten-native-proofs-independently-kernel-recheck
  (let [{:keys [environment results]} @checked-corpus]
    (is (= 10 (count results)))
    (is (= 8 (count (set (map #(get-in % [:claim :foreign/name]) results)))))
    (is (= #{:identity-assumption :constant-assumption :apply-function
             :transitivity-apply :nat-identity :nat-zero :nat-successor
             :identity-exact :transitivity-exact}
           (set (map #(get-in % [:job :plan]) results))))
    (doseq [{:keys [result declaration job]} results]
      (let [persisted (environment/declaration environment (:rainbow/id declaration))
            checked (kernel/check environment (:rainbow/value persisted)
                                  (:rainbow/type persisted)
                                  (set (:rainbow/universes persisted)))]
        (is (= :proved (:status result)) (str (:name job)))
        (is (= :checked (:status checked)) (str (:name job)))
        (is (= #{} (kernel/axioms environment (:name job))))))))

(deftest foreign-native-relationships-check-types-and-dependency-exclusion
  (let [{:keys [relationships]} @checked-corpus]
    (is (= 10 (count relationships)))
    (doseq [relationship relationships]
      (is (= :same-type (:relation relationship)))
      (is (true? (:type-check relationship)))
      (is (true? (:foreign-proof-hidden? relationship)))
      (is (= #{} (:foreign-proof-dependencies relationship))))))

(deftest independent-reproof-environment-replays-in-a-fresh-jvm
  (let [path "artifacts/day13/environment.edn"
        replay (java-command "-m" "rainbow.history.lean-hidden-body-inhabitation" "replay" path)
        reports (repeatedly 2 #(java-command "-m" "rainbow.history.lean-hidden-body-inhabitation"))]
    (is (zero? (:exit replay)) (:err replay))
    (is (.contains ^String (:out replay) ":status :replayed"))
    (is (every? #(zero? (:exit %)) reports))
    (is (= 1 (count (set (map :out reports)))))))
