(ns rainbow.proving-loop-benchmark-proofs-test
  "The four proving-loop benchmark goals, proved through the proving loop on 2026-10-26
  (artifacts/proving-loop/2026-10-26/benchmark-proofs.edn; each entry says how it was found: search,
  AI proposal, or hand-written after the search returned the goal blocked). Every proof is replayed
  here through kernel/add-declaration on the D63 checkpoint plus the modules the goals use, and each
  benchmark statement is rebuilt from the definitions of the benchmark script (it drives the proving loop and ships with Rainbow Pro)."
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sums.value-algebra :as s]
            [rainbow.math.logic.function :as f]
            [rainbow.module :as module]
            [rainbow.term :as term]))

(def env0 (delay (reduce module/install-module
                         (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz"))
                         '[rainbow.math.sums.value-algebra rainbow.math.nat.at-most-add rainbow.math.nat.divmod])))
(def entries (edn/read-string (slurp "artifacts/proving-loop/2026-10-26/benchmark-proofs.edn")))

(defn- install [env {:keys [alias proved]}]
  (let [{:keys [type proof]} proved
        r (kernel/add-declaration env {:rainbow/kind :theorem :rainbow/aliases #{alias} :rainbow/universes []
                                       :rainbow/type type :rainbow/value proof :rainbow/transparency :opaque
                                       :rainbow/dependencies (into (term/constants type) (term/constants proof))
                                       :rainbow/provenance {:origin :native :producer :claude-proving-loop}
                                       :rainbow/schema-version 1})]
    (is (= :accepted (:status r)) (str alias))
    (:environment r)))

;; the benchmark statements, as the benchmark script (Rainbow Pro) states them
(def nat s/nat) (def idx (f/arrow nat nat))
(defn- app [g & xs] (apply f/app g xs))
(defn- le [a b] (s/call 'nat/at-most a b)) (defn- add [a b] (s/call 'algebra/nat-add a b))
(defn- eq [a b] (f/equality [:succ [:zero]] nat a b))
(defn- st [i] (app 'start i)) (defn- end [i] (add (app 'len i) (st i)))
(def chain (f/forall [['i nat] ['hi (s/below 'i 'm)]] (eq (st (s/succ 'i)) (end 'i))))
(def chain-binders [['start idx] ['len idx] ['m nat] ['chain chain]])
(def benchmark
  {'loop/successor-bound (f/forall [['q nat] ['m nat] ['h (le (s/succ 'q) 'm)]] (le 'q 'm))
   'loop/three-transitive (f/forall [['a nat] ['b nat] ['c nat] ['d nat] ['ab (le 'a 'b)] ['bc (le 'b 'c)] ['cd (le 'c 'd)]] (le 'a 'd))
   'loop/range-start-monotone (f/forall (into chain-binders [['a nat] ['b nat] ['ha (le 'a 'b)] ['hb (le 'b 'm)]]) (le (st 'a) (st 'b)))
   'loop/range-unique (f/forall (into chain-binders [['j nat] ['j2 nat] ['t nat] ['hj (s/below 'j 'm)] ['hj2 (s/below 'j2 'm)]
                                                      ['lower (le (st 'j) 't)] ['upper (s/below 't (end 'j))]
                                                      ['lower2 (le (st 'j2) 't)] ['upper2 (s/below 't (end 'j2))]]) (eq 'j 'j2))})

(deftest the-loop-proved-the-four-benchmark-goals
  (let [env (reduce install @env0 entries)]
    (doseq [{:keys [alias how]} entries]
      (testing (str alias)
        (is (string? how) "each proof records how it was found")
        (is (= #{} (kernel/axioms env alias)) "axiom-free")))
    (doseq [[alias surface] benchmark]
      (testing (str alias " states the benchmark goal")
        (is (= (:term (elaborate/core-expression env surface))
               (:rainbow/type (environment/declaration env (environment/resolve-id env alias)))))))))
