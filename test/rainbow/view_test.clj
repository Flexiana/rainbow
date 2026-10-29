(ns rainbow.view-test
  "The Proof Explorer (lein explore): its data on small environments (the direct-term corpus, and a
  natural-number fixture whose example values the kernel computes), the page files, and proof
  bundles (replayed, claims shown, refused when the kernel or the base disagrees)."
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.test :refer [deftest is testing]]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.data.inductive :as inductive]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.persistence]
            [rainbow.term :as term]
            [rainbow.view :as view]))

;; ---------------------------------------------------------------- a JSON reader, so the files are read back as JSON

(defn- parse-json [^String s]
  (let [i (volatile! 0)
        peek* #(when (< @i (count s)) (.charAt s @i))
        ws #(while (and (peek*) (Character/isWhitespace (char (peek*)))) (vswap! i inc))
        expect (fn [^String t] (assert (.startsWith s t @i) (str "JSON: expected " t " at " @i)) (vswap! i + (count t)))]
    (letfn [(value []
              (ws)
              (let [c (peek*)]
                (case c
                  \{ (do (expect "{") (ws)
                         (if (= \} (peek*)) (do (expect "}") {})
                             (loop [m {}] (ws) (let [k (string*)] (ws) (expect ":") (let [m (assoc m k (value))] (ws)
                                                                                         (if (= \, (peek*)) (do (expect ",") (recur m)) (do (expect "}") m)))))))
                  \[ (do (expect "[") (ws)
                         (if (= \] (peek*)) (do (expect "]") [])
                             (loop [v []] (let [v (conj v (value))] (ws) (if (= \, (peek*)) (do (expect ",") (recur v)) (do (expect "]") v))))))
                  \" (string*)
                  \t (do (expect "true") true) \f (do (expect "false") false) \n (do (expect "null") nil)
                  (let [m (re-find #"^-?\d+(\.\d+)?([eE][-+]?\d+)?" (subs s @i))] (assert m (str "JSON: bad value at " @i))
                       (vswap! i + (count (first m))) (if (second m) (Double/parseDouble (first m)) (parse-long (first m)))))))
            (string* []
              (expect "\"")
              (let [sb (StringBuilder.)]
                (loop []
                  (let [c (.charAt s @i)]
                    (vswap! i inc)
                    (cond (= c \") (str sb)
                          (= c \\) (let [e (.charAt s @i)]
                                     (vswap! i inc)
                                     (if (= e \u) (do (.append sb (char (Integer/parseInt (subs s @i (+ @i 4)) 16))) (vswap! i + 4))
                                         (.append sb (case e \n \newline \t \tab \r \return \b \backspace \f \formfeed e)))
                                     (recur))
                          :else (do (.append sb c) (recur)))))))]
      (let [v (value)] (ws) (assert (= @i (count s)) "JSON: trailing text") v))))

(defn- tmp-dir [label] (str (doto (java.io.File/createTempFile (str "rainbow-view-" label) "") (.delete))))

;; ---------------------------------------------------------------- the Proof Explorer

(deftest the-direct-term-corpus-exports-every-declaration
  (let [env (direct-term-corpus/build-environment)
        dir (tmp-dir "day1")
        data (view/explorer-data env {:source {:kind "checkpoint" :path "day1"}})
        _ (view/write-page! dir "scripts/proof-explorer.html" "data.json" data false)
        json (parse-json (slurp (io/file dir "data.json")))]
    (testing "every theorem of the corpus is a root, and the closure adds nothing (no dependencies)"
      (is (= (count direct-term-corpus/proofs) (count (get json "nodes")) (count (get json "roots"))))
      (is (= (set (map (comp str :name) direct-term-corpus/proofs)) (set (map #(get % "alias") (get json "nodes"))))))
    (testing "each node carries the kernel's facts"
      (doseq [n (get json "nodes")]
        (is (= "theorem" (get n "kind")))
        (is (= [] (get n "axioms")) "the direct-term proofs use no axiom")
        (is (= "assume" (get-in n ["proof" "k"])) "every proof here starts with a lambda")
        (is (string/starts-with? (get n "statement") (get n "alias")))))
    (is (= (environment/environment-id env) (get json "environment")))
    (testing "the page carries the same data inline, so it opens from disk"
      (let [html (slurp (io/file dir "index.html"))
            inline (second (re-find #"(?s)<script id=\"rainbow-data\" type=\"application/json\">(.*?)</script>" html))]
        (is (= json (parse-json inline)))
        (is (not (string/includes? html "/*RAINBOW-DATA*/")))
        (is (string/includes? html "integrity=\"sha384-"))))))

(defn- nat-fixture
  "The direct-term corpus with Nat and equality (rainbow.data.inductive), plus a definition and two
  theorems about it, each added by the kernel."
  []
  (let [nat (f/const* 'data/Nat []) succ #(f/app (f/const* 'data/succ []) %) level [:succ [:zero]]
        add-two #(f/app (f/const* 'fixture/add-two []) %)
        add (fn [env kind alias type value]
              (let [core #(:term (elaborate/core-expression env %)) t (core type) v (core value)
                    r (kernel/add-declaration env {:rainbow/kind kind :rainbow/aliases #{alias} :rainbow/universes []
                                                   :rainbow/type t :rainbow/value v
                                                   :rainbow/transparency (if (= :definition kind) :reducible :opaque)
                                                   :rainbow/dependencies (into (term/constants t) (term/constants v))
                                                   :rainbow/provenance {:origin :native :producer :view-test} :rainbow/schema-version 1})]
                (assert (= :accepted (:status r)) (pr-str (dissoc r :environment)))
                (:environment r)))]
    (-> (inductive/build-environment)
        (add :definition 'fixture/add-two (f/arrow nat nat) (f/lam [['n nat]] (succ (succ 'n))))
        (add :theorem 'fixture/add-two-unfolds (f/forall [['n nat]] (f/equality level nat (add-two 'n) (succ (succ 'n))))
             (f/lam [['n nat]] (f/app (f/const* 'equality/reflexive [level]) nat (succ (succ 'n)))))
        (add :theorem 'fixture/add-two-twice (f/forall [['m nat] ['n nat]] (f/equality level nat (add-two (add-two 'm)) (succ (succ (succ (succ 'm))))))
             (f/lam [['m nat] ['n nat]] (f/app (f/const* 'equality/reflexive [level]) nat (succ (succ (succ (succ 'm))))))))))

(deftest example-values-are-computed-by-the-kernel
  (let [env (nat-fixture)
        roots (map #(environment/resolve-id env %) '[fixture/add-two-unfolds fixture/add-two-twice])
        dir (tmp-dir "nat")
        _ (view/write-page! dir "scripts/proof-explorer.html" "data.json" (view/explorer-data env {:roots roots}) true)
        json (parse-json (slurp (io/file dir "data.json")))
        by-alias (into {} (map (juxt #(get % "alias") identity) (get json "nodes")))
        unfolds (by-alias "fixture/add-two-unfolds")]
    (testing "the closure of the two roots: themselves, the definition, Nat, its constructors, Eq and reflexivity"
      (is (= 2 (count (get json "roots"))))
      (is (= (count (into #{} (mapcat #(tree-seq (constantly true) (fn [id] (:rainbow/dependencies (environment/declaration env id))) %)) roots))
             (count (get json "nodes"))))
      (is (every? by-alias ["fixture/add-two" "data/Nat" "data/succ" "equality/Eq" "equality/reflexive"])))
    (testing "the first input row is 2: add-two 2 and succ (succ 2) both normalize to 4"
      (let [row (first (get unfolds "examples"))]
        (is (= "nat" (get row "type")))
        (is (= [2] (get row "inputs")))
        (is (= 4 (get row "lhs") (get row "rhs")))
        (is (true? (get row "equal")))
        (is (some #(= {"expr" "(fixture/add-two 2)" "value" 4} %) (get row "steps")))))
    (testing "every row agrees with the kernel's own normalization of the instantiated sides"
      (doseq [row (get unfolds "examples") :let [[n] (get row "inputs")]]
        (is (= (+ n 2) (get row "lhs") (get row "rhs")))
        (is (= {:status :normalized :term [:nat (+ n 2)]}
               (select-keys (kernel/normalize env [:app [:const (environment/resolve-id env 'fixture/add-two) []] [:nat n]] {:rainbow.kernel/literals true}) [:status :term])))))
    (testing "two binders, one unused"
      (is (every? #(= 2 (count (get % "inputs"))) (get-in by-alias ["fixture/add-two-twice" "examples"])))
      (is (= "assume" (get-in by-alias ["fixture/add-two-twice" "proof" "k"]))))
    (testing "a definition gets no examples, and its statement comes from the renderer"
      (is (nil? (get-in by-alias ["fixture/add-two" "examples"])))
      (is (string/starts-with? (get-in by-alias ["fixture/add-two" "statement"]) "fixture/add-two :")))
    (testing "--offline inlines the vendored libraries and drops every network reference"
      (let [html (slurp (io/file dir "index.html"))]
        (is (not (re-find #"<script src=" html)))
        (is (not (re-find #"fonts\.googleapis|cdnjs|cdn\.jsdelivr" html)))
        (is (string/includes? html (subs (slurp "scripts/cytoscape-3.28.1.min.js") 0 200)))))))

;; ---------------------------------------------------------------- a proof bundle on the default checkpoint

(def ^:private default-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")

(deftest a-proof-bundle-is-replayed-and-its-claims-shown
  (let [base (:environment (checkpoint/load-checkpoint default-checkpoint))
        nat (f/const* 'data/Nat []) level [:succ [:zero]]
        core #(:term (elaborate/core-expression base %))
        t (core (f/forall [['n nat]] (f/equality level nat 'n 'n)))
        v (core (f/lam [['n nat]] (f/app (f/const* 'equality/reflexive [level]) nat 'n)))
        r (kernel/add-declaration base {:rainbow/kind :theorem :rainbow/aliases #{'bundle/self-equal} :rainbow/universes []
                                        :rainbow/type t :rainbow/value v :rainbow/transparency :opaque
                                        :rainbow/dependencies (into (term/constants t) (term/constants v))
                                        :rainbow/provenance {:origin :native :producer :view-test} :rainbow/schema-version 1})
        id (environment/resolve-id (:environment r) 'bundle/self-equal)
        bundle {:rainbow.bundle/schema-version 1
                :base {:checkpoint default-checkpoint :modules []
                       :environment-id (environment/environment-id base) :names-id (rainbow.persistence/names-id base)}
                :claims {'bundle/self-equal {:id id :axioms #{}}}
                :declarations [(environment/declaration (:environment r) id)]}
        write (fn [b] (let [f (str (tmp-dir "bundle") ".edn")] (spit f (pr-str b)) f))
        dir (tmp-dir "bundle-page")
        data (view/explore! (write bundle) dir {})]
    (is (= :accepted (:status r)))
    (testing "the default roots are the bundle's claims"
      (is (= [id] (:roots data)))
      (is (= [{:alias "bundle/self-equal" :id id :resolved id :axioms [] :ok true}] (:claims data)))
      (is (= "bundle" (get-in data [:source :kind])))
      (is (= (environment/environment-id base) (:baseEnvironment data))))
    (testing "a claim whose recorded axioms differ from the kernel's is shown as not matching"
      (let [wrong (assoc-in bundle [:claims 'bundle/self-equal :axioms] #{"sha256:0"})]
        (is (= [false] (map :ok (:claims (view/explore! (write wrong) dir {})))))))
    (testing "a bundle whose proof the kernel rejects is refused"
      (let [wrong (assoc-in bundle [:declarations 0 :rainbow/value] (core (f/lam [['n nat]] 'n)))]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"kernel rejected bundle entry" (view/explore! (write wrong) dir {})))))
    (testing "a bundle whose base does not reproduce its environment id is refused"
      (let [wrong (assoc-in bundle [:base :environment-id] "sha256:0")]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"environment id" (view/explore! (write wrong) dir {})))))))
