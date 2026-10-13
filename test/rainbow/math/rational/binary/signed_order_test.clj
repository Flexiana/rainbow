(ns rainbow.math.rational.binary.signed-order-test
  "The SIGNED bridge (on top of brick 5b): the checker's actual hot decision
  signed/decide-at-most, expressed on the Bin layer, proved to agree with -- and to
  entail the soundness of -- the trusted signed order.

  Runs from a COLD JVM. Verifies the three bridge declarations are checked +
  axiom-free. They are thin instances of the brick-5b nnrat-level lemmas at
  l := (pos a + neg b), r := (pos b + neg a) -- the two cross-SUMS that
  signed/decide-at-most and signed/at-most reduce to -- so the substantive content is
  that those defeqs hold and the whole thing type-checks axiom-free."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.data.binary :as binary]
            [rainbow.math.rational.binary.rational-order :as bro]
            [rainbow.math.rational.binary.signed-order :as bso]
            [rainbow.math.rational.signed.decide-order :as sdo]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def ^:private env
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          sdo/extend-environment
          binary/extend-environment
          bro/extend-environment
          bso/extend-environment))))

(defn- checked-and-axiom-free? [e alias]
  (let [id (environment/resolve-id e alias)
        d (environment/declaration e id)]
    (and id
         (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d)
                                            (set (:rainbow/universes d)))))
         (= #{} (kernel/axioms e id)))))

(deftest bin-signed-bridge-is-checked-and-axiom-free
  (testing "the signed-level bridge is checked + axiom-free: the Bin decision equals
            signed/decide-at-most a b and entails the trusted signed order both ways"
    (let [e @env]
      (is (checked-and-axiom-free? e 'bin/decide-signed-matches)
          "Bin decision = signed/decide-at-most a b (when the Bin fields represent the
           two cross-sums' num/den)")
      (is (checked-and-axiom-free? e 'bin/decide-signed-sound)
          "decide=true -> signed/at-most a b (the trusted order)")
      (is (checked-and-axiom-free? e 'bin/decide-signed-false-reverse)
          "decide=false -> signed/at-most b a")
      (is (checked-and-axiom-free? e 'bin/decide-signed-sound-from-parts)
          "capstone: from Bin reps of the 4 signed parts, decide=true -> signed/at-most a b
           (cross-sums built on Bin; no unary Nat of the magnitude materialised)"))))
