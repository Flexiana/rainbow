(ns rainbow.kernel-content-id-collision-test
  "B-20261030-16 (P0): content ids were not injective. canonical/sha256 hashes UTF-8 bytes and Java
  encodes an unpaired UTF-16 surrogate as \"?\", so (symbol \"\\uD800\") and (symbol \"?\") gave two
  declarations one id; add-declaration then replaced the stored declaration while declarations checked
  against the first stayed, and under the proof-irrelevance profile the kernel accepted a proof of False
  (probe: kernel_adversarial_probe_test.clj on bugs-kernel-probe, 17af09f7).

  Two independent guards, each tested with the other switched off:
  - canonical.clj refuses an unpaired surrogate (:canonical/unsupported-value);
  - kernel.clj refuses an id that already names different content (:kernel/content-id-collision), in
    add-declaration and in add-inductive-block.
  Ids of well-formed content do not change: the last test pins ids recorded before the patch."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.canonical :as canonical]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.profile :as profile]
            [rainbow.persistence :as persistence]
            [rainbow.term :as term]))

(def ^:private checkpoint-path "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")

(def ^:private replayed (delay (checkpoint/load-checkpoint checkpoint-path)))

(def ^:private base
  (delay (let [cp @replayed]
           (when-not (= :replayed (:status cp)) (throw (ex-info "Checkpoint rejected" {:status (:status cp)})))
           (:environment cp))))

(def ^:private Z [:zero])
(def ^:private O [:succ [:zero]])

(defn- id [env alias]
  (or (environment/resolve-id env alias) (throw (ex-info "missing alias" {:alias alias}))))
(defn- category [r] (get-in r [:error :error/category]))
(defn- rejected? [r] (and (= :rejected (:status r)) (keyword? (category r))))

(defn- definition [alias universes type value]
  {:rainbow/kind :definition :rainbow/aliases #{alias} :rainbow/universes universes
   :rainbow/type type :rainbow/value value :rainbow/transparency :reducible
   :rainbow/dependencies (into (term/constants type) (term/constants value))})

(defn- block [alias level universes parameters constructors]
  {:block/schema-version 1 :block/alias alias :block/universes universes :block/parameters parameters
   :block/sort-level level
   :block/constructors (vec (map-indexed (fn [i fields] {:constructor/alias (symbol "probe" (str (name alias) "-c" i))
                                                         :constructor/fields fields})
                                         constructors))})

(defn- canonical-category [value]
  (try (canonical/encode value) nil
       (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))

(defmacro ^:private without-canonical-guard
  "Runs body with the canonical surrogate guard switched off, to test the kernel guard on its own."
  [& body]
  `(with-redefs [rainbow.canonical/unpaired-surrogate? (constantly false)] ~@body))

;; The probe's two declarations: pick.{p,q} : Sort (p+1) := Sort p and pick.{p,q} : Sort (q+1) := Sort q.
(def ^:private p (symbol "\uD800"))
(def ^:private q (symbol "?"))
(defn- pick [universe-name]
  (definition 'probe/pick [p q] [:sort [:succ [:param universe-name]]] [:sort [:param universe-name]]))

;; ---- canonical guard ----------------------------------------------------------------------------

(deftest unpaired-surrogates-are-refused-by-the-canonical-encoding
  (doseq [value ["\uD800" "\uDC00" "a\uD800" "\uD800a" "\uDC00\uD800" "\uD83D\uD83D\uDE00"
                 (symbol "\uD800") (keyword "\uDFFF") #{"\uD800"} {"\uD800" 1} {:k ["x" (symbol "u" "\uDBFF")]}]]
    (is (= :canonical/unsupported-value (canonical-category value)) (pr-str (map int (str value)))))
  (testing "well-formed strings, including a surrogate pair, still encode"
    (doseq [value ["" "?" "\u03bb" "\uD83D\uDE00" (symbol "\uD83D\uDE00")]]
      (is (string? (canonical/encode value)))))
  (testing "the probe's colliding names no longer share an id: the surrogate one has none"
    (is (= :canonical/unsupported-value (canonical-category p)))
    (is (string? (canonical/content-id q))))
  (testing "add-declaration refuses the surrogate declaration instead of throwing"
    (let [r (kernel/add-declaration @base (pick p))]
      (is (= :rejected (:status r)))
      (is (= :canonical/unsupported-value (category r))))))

;; ---- kernel guard: add-declaration --------------------------------------------------------------

(deftest colliding-declaration-is-refused-by-the-kernel-without-the-canonical-guard
  (without-canonical-guard
   (is (= (canonical/content-id p) (canonical/content-id q))
       "lever check: with the canonical guard off the collision exists")
   (let [r1 (kernel/add-declaration @base (pick p))
         pick-id (:rainbow/id (:declaration r1))
         r2 (kernel/add-declaration (:environment r1) (pick q))]
     (is (= :accepted (:status r1)))
     (is (= pick-id (environment/declaration-id (assoc (pick q) :rainbow/schema-version 1)))
         "the second pick computes the same id")
     (is (= :kernel/content-id-collision (category r2)))
     (is (= {:id pick-id} (select-keys (:error r2) [:id])))
     (is (= [:sort [:param p]] (:rainbow/value (environment/declaration (:environment r1) pick-id)))
         "the stored declaration is untouched"))))

(defn- proof-of-false
  "The probe's derivation: N : pick.{1,0} := Nat, then under proof irrelevance 0 = 1 in N, so Nat.rec
  maps 0 to truth and 1 to falsity. Returns the kernel's check result in env."
  [env]
  (let [envp (:environment (profile/activate env :proof-irrelevant))
        N (f/const* 'probe/N []) natc (f/const* 'data/Nat [])
        T (f/const* 'proposition/truth []) F (f/const* 'proposition/falsity [])
        a (f/const* 'data/zero []) b (f/app (f/const* 'data/succ []) a)
        h (f/app (f/const* 'logic/proof-irrelevance []) N a b)
        D (f/lam [['k N]] (f/app (f/const* 'data/Nat.rec [O]) (f/lam [['m natc]] 'Prop) T
                                 (f/lam [['m natc] ['ih 'Prop]] F) 'k))
        proof (f/app (f/const* 'equality/substitution [Z]) N a b h D (f/const* 'proposition/trivial []))
        core (fn [surface] (let [r (elaborate/core-expression envp surface)]
                             (or (:term r) (throw (ex-info "elaboration failed" {:result r})))))]
    (kernel/check envp (core proof) (core F) #{})))

(deftest the-probe-derivation-of-false-is-refused
  (testing "with both guards: the first pick is already refused, so N cannot be stated"
    (is (= :canonical/unsupported-value (category (kernel/add-declaration @base (pick p))))))
  (testing "kernel guard alone"
    (without-canonical-guard
     (let [nat-id (id @base 'data/Nat)
           r1 (kernel/add-declaration @base (pick p))
           pick-id (:rainbow/id (:declaration r1))
           r2 (kernel/add-declaration (:environment r1)
                                      (definition 'probe/N [] [:const pick-id [O Z]] [:const nat-id []]))
           r3 (kernel/add-declaration (:environment r2) (pick q))
           env (:environment r2)]
       (is (= :accepted (:status r1) (:status r2)))
       (is (= :kernel/content-id-collision (category r3)) "the swap that enabled the proof is refused")
       (is (rejected? (proof-of-false env)) "the environment the kernel keeps refuses the proof of False")
       (testing "control: the same proof IS accepted if the swap is forced outside the kernel, so the
                  refusal above is what closes the hole"
         (let [swapped (assoc-in env [:rainbow.environment/declarations pick-id :rainbow/value]
                                 [:sort [:param q]])
               swapped (assoc-in swapped [:rainbow.environment/declarations pick-id :rainbow/type]
                                 [:sort [:succ [:param q]]])]
           (is (= :checked (:status (proof-of-false swapped))))))))))

;; ---- legitimate re-adds still work -----------------------------------------------------------------

(deftest identical-re-adds-are-accepted-with-the-same-id
  (let [d (definition 'probe/two [] [:const (id @base 'data/Nat) []] [:nat 2])
        r1 (kernel/add-declaration @base d)
        did (:rainbow/id (:declaration r1))
        r2 (kernel/add-declaration (:environment r1) d)
        r3 (kernel/add-declaration (:environment r2) (assoc d :rainbow/aliases #{'probe/two-again}))
        env3 (:environment r3)]
    (is (= :accepted (:status r1) (:status r2) (:status r3)))
    (is (= did (:rainbow/id (:declaration r2)) (:rainbow/id (:declaration r3))))
    (is (= did (id env3 'probe/two) (id env3 'probe/two-again)) "both aliases name the one id")
    (is (= #{'probe/two 'probe/two-again} (:rainbow/aliases (environment/declaration env3 did))))
    (is (= 1 (count (filter #{did} (:rainbow.environment/order env3)))) "no duplicate order entry")
    (is (= (environment/environment-id (:environment r1)) (environment/environment-id env3))))
  (testing "a recorded checkpoint declaration re-added, with and without a new alias, keeps its id"
    (doseq [alias '[algebra/nat-add nat/add-commutative equality/reflexive]]
      (let [did (id @base alias)
            stored (environment/declaration @base did)
            r (kernel/add-declaration @base stored)
            r-alias (kernel/add-declaration @base (update stored :rainbow/aliases conj 'probe/re-added))]
        (is (= :accepted (:status r) (:status r-alias)) (str alias))
        (is (= did (:rainbow/id (:declaration r)) (:rainbow/id (:declaration r-alias))) (str alias))
        (is (= did (id (:environment r-alias) 'probe/re-added)) (str alias))
        (is (= (environment/environment-id @base)
               (environment/environment-id (:environment r))
               (environment/environment-id (:environment r-alias))) (str alias))))))

(deftest identical-block-re-adds-are-accepted-with-the-same-id
  (let [A {:parameter/name 'A :parameter/type [:sort [:succ [:param 'u]]]}
        spec (block 'probe/Box [:succ [:param 'u]] '[u] [A] [[{:field/name 'a :field/type [:var 'A]}]])
        r1 (kernel/add-inductive-block @base spec)
        bid (:rainbow/id (:block r1))
        renamed (-> (block 'probe/Box2 [:succ [:param 'v]] '[v]
                           [{:parameter/name 'B :parameter/type [:sort [:succ [:param 'v]]]}]
                           [[{:field/name 'b :field/type [:var 'B]}]]))
        r2 (kernel/add-inductive-block (:environment r1) renamed)]
    (is (= :accepted (:status r1)))
    (is (= :accepted (:status r2)) "same semantic block under fresh aliases and renamed universe/binders")
    (is (= bid (:rainbow/id (:block r2))))
    (is (= (id (:environment r1) 'probe/Box) (id (:environment r2) 'probe/Box2)))
    (is (= :kernel/alias-conflict (category (kernel/add-inductive-block (:environment r1) spec)))
        "an exact re-add with the same aliases is refused by alias, as before")))

;; ---- kernel guard: add-inductive-block ----------------------------------------------------------

(deftest colliding-inductive-block-is-refused
  (let [nat-id (id @base 'data/Nat)
        nat-block-id (:rainbow/block-id (environment/declaration @base nat-id))
        unit (block 'probe/Unit O [] [] [[]])]
    (is (string? nat-block-id))
    (testing "control: without a collision the block is accepted under its own id"
      (let [r (kernel/add-inductive-block @base unit)]
        (is (= :accepted (:status r)))
        (is (not= nat-block-id (:rainbow/id (:block r))))))
    (testing "a different block whose id equals Nat's block id is refused"
      (with-redefs [kernel/inductive-block-id (constantly nat-block-id)]
        (let [r (kernel/add-inductive-block @base unit)]
          (is (= :kernel/content-id-collision (category r)))
          (is (= nat-block-id (get-in r [:error :id]))))))
    (testing "a new block whose member id already names a stored declaration is refused"
      (let [orig @#'kernel/member-id
            nat-add-id (id @base 'algebra/nat-add)]
        (with-redefs [kernel/member-id (fn [block-id member-key]
                                         (if (= :inductive member-key) nat-add-id (orig block-id member-key)))]
          (let [r (kernel/add-inductive-block @base unit)]
            (is (= :kernel/content-id-collision (category r)))
            (is (= nat-add-id (get-in r [:error :id])))))))))

;; ---- recorded ids are unchanged ------------------------------------------------------------------

;; Captured on origin/release-1.5.0 (13a0f4f7), before either guard, by replaying the d63 checkpoint.
(def ^:private recorded-ids
  {:environment-id "sha256:a41ba35a9f845aa04600620234dd1ccbb86969b09ffb14a44847da82ba4a5d5c"
   :names-id "sha256:04959786090003bdfd133d7f4da521566de7ede77813ee1fa8aa3185284d193a"
   :declarations 2197
   :all-declaration-ids-digest "sha256:a7db13142f9f21a1710e28b2e7ab7fa20f293969fea5ef37b54092105f4c256c"
   :all-block-ids-digest "sha256:d31a12dd40e7c6833c934f89465b069a8cf886446803d755b4b74f3e8b69d517"
   :nat-block "sha256:9502f9811412a3a0b0ea66e9023d47af8c9282cd0796a9806b55457a2b9f9a8f"
   :aliases '{data/Nat "sha256:3506a443d496ca97e5476cbbb47baadc33ccaef5a3e9717e4bcac7c83acc1453"
              data/zero "sha256:11ea4dcb19455ac6d98fa23f4a631c8e72e1d5158d55f35d15a6891da156837a"
              data/succ "sha256:2c087b95d40cd6088f7ed5b2c005939be25c07dd402f56d99fa9cd076fa760b5"
              data/Nat.rec "sha256:4e582552da253928d15815a19cb046fe00b97a31791aff439687909bf8eea98a"
              equality/Eq "sha256:2d47fcd5253cdc0f5e0c62e79782ace49ee9d55c714521dc2d420111d3828beb"
              equality/reflexive "sha256:12530ecfc35471f5b7753d0d46928af923e852495b7dea8a5e6b62e7a2783c24"
              algebra/nat-add "sha256:ae52ec6e6d33d320ad5cf5bf04a0b7d7a6170f1553ca6921d296cb8f7452b7c5"
              nat/add-commutative "sha256:a0a8805124aed22ef2a789b59b6c6bc9b12b0974c99d0df898f2c6ab7068c29b"
              proposition/falsity "sha256:f9999f3e33ce2333ccf790fd50d8fad18804dce4b4b74f571402591c8dba09d6"
              proposition/truth "sha256:a5d13ae2df14d9a452f3cc2146b31c04a8b266b2a09c20ca5bc226fd9ea552ea"}
   ;; also checked outside the JVM: printf 's1:?' | shasum -a 256, and so on
   :strings {"" "sha256:fb912574cecad54c6a0bc75b46172350b6374929d602d5fbcb4ca0ec831fd532"
             "?" "sha256:7494b1f5e93de3644aba0298d4447cb955cacd316f2ca66001118d8bedaf54ea"
             "\u03bb" "sha256:3f5c1f81848359259087f449e195d1efac3cd6ad5ee68d7a5547774b8c507500"
             "\uD83D\uDE00" "sha256:4adfbd44a26e51dd4bec26601c6cb40644dcfd065af594a4f29c28c6d460d9ce"
             "data/Nat" "sha256:03e0846cb5352fb8f00a91626885fd50650b3c44199255fe03fc60b7e8d9d691"}})

(deftest existing-ids-are-unchanged
  (let [env @base]
    (is (= :replayed (:status @replayed)) "the recorded checkpoint replays: every supplied id and its environment id match")
    (is (= (:environment-id recorded-ids) (environment/environment-id env)))
    (is (= (:names-id recorded-ids) (persistence/names-id env)))
    (is (= (:declarations recorded-ids) (count (:rainbow.environment/declarations env))))
    (is (= (:all-declaration-ids-digest recorded-ids)
           (canonical/sha256 (apply str (sort (keys (:rainbow.environment/declarations env)))))))
    (is (= (:all-block-ids-digest recorded-ids)
           (canonical/sha256 (apply str (sort (keys (:rainbow.environment/blocks env)))))))
    (is (= (:nat-block recorded-ids) (:rainbow/block-id (environment/declaration env (id env 'data/Nat)))))
    (doseq [[alias expected] (:aliases recorded-ids)]
      (is (= expected (environment/resolve-id env alias)) (str alias)))
    (doseq [[s expected] (:strings recorded-ids)]
      (is (= expected (canonical/content-id s)) (pr-str (map int s))))))
