(ns rainbow.bundle-binary-test
  "The binary file format for shared bundles: an exact encoding of the schema-3 map,
  checked like any bundle, with every malformed or tampered file refused -- by the
  unpacker, the shared decoder or the kernel, never accepted with other claims."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.canonical]
            [rainbow.bundle.binary :as binary]
            [rainbow.bundle.shared :as shared]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.data.inductive :as inductive]
            [rainbow.environment :as environment]
            [rainbow.history.direct-term-corpus :as corpus]
            [rainbow.kernel :as kernel]
            [rainbow.main :as main]))

(def ^:private empty-env (environment/empty-environment))
(def ^:private checked-env (delay (corpus/build-environment)))
(defn- plain []
  (main/proof-bundle {:checkpoint "test-base" :modules [] :base-env empty-env :env @checked-env
                      :claims (map :name corpus/proofs)}))
(defmacro ^:private on-test-base [& body]
  `(with-redefs [checkpoint/load-checkpoint (fn [_#] {:status :replayed :environment empty-env})] ~@body))

(defn- verdict [^bytes data]
  ;; what verify does with a file: unpack, decode, check -- a refusal anywhere is a FAIL
  (on-test-base
   (try (main/check-bundle (binary/unpack data))
        (catch clojure.lang.ExceptionInfo e {:ok? false :error (.getMessage e)}))))

(deftest packing-is-exact
  (let [s (shared/encode (plain))
        block (kernel/add-inductive-block @checked-env inductive/bool-spec)
        b2 (assoc (main/proof-bundle {:checkpoint "b" :modules [] :base-env @checked-env :env (:environment block) :claims []}) :claims {})
        literal (assoc-in (plain) [:declarations 0 :rainbow/type] [:pi [:sort [:zero]] [:nat 123456789012345678901234567890] :explicit])]
    (doseq [[what bundle] [["schema 1" (plain)] ["schema 2 (a block)" b2] ["a literal beyond Long" literal]]]
      (testing what
        (let [s (shared/encode bundle)]
          (is (= s (binary/unpack (binary/pack s))))
          (is (= bundle (shared/decode (binary/unpack (binary/pack s))))))))
    (is (< (alength (binary/pack s)) (count (pr-str s))))))

(deftest a-binary-bundle-is-checked-like-the-plain-one
  (let [plain-result (on-test-base (main/check-bundle (plain)))
        binary-result (verdict (binary/pack (shared/encode (plain))))]
    (is (true? (:ok? plain-result)))
    (is (true? (:ok? binary-result)) (pr-str binary-result))
    (is (= (:claims plain-result) (:claims binary-result)))))

;; ---- mutation sweep ------------------------------------------------------------
;; Every mutated file must be refused (by the unpacker, the shared decoder or the
;; kernel), decode to exactly the original bundle, or be accepted with exactly the
;; original claims. Bundles are compared by canonical encoding, which orders keys by
;; their encoding (= on a sorted map can throw when a mutation changes a key's type).
;; By default a deterministic sample runs; RAINBOW_EXHAUSTIVE_SWEEP=1 runs all 255
;; substitutions and all 256 insertions at every position, every deletion, and
;; 100,000 seeded multi-byte edits.

(def ^:private exhaustive? (= "1" (System/getenv "RAINBOW_EXHAUSTIVE_SWEEP")))

(defn- canon [x] (try (rainbow.canonical/encode x) (catch Throwable _ ::unencodable)))

(defn- classify [^bytes data original expected-claims]
  (let [decoded (try (shared/decode (binary/unpack data)) (catch Throwable _ ::refused))]
    (cond
      (= ::refused decoded) :refused
      (= (canon decoded) original) :original
      :else (let [r (on-test-base (main/check-bundle decoded))]
              (cond (not (:ok? r)) :refused
                    (= (canon (:claims r)) expected-claims) :same-claims
                    :else :OTHER-CLAIMS)))))

(defn- substitute [^bytes b i v] (doto (aclone b) (aset-byte (int i) (unchecked-byte v))))
(defn- insert [^bytes b i v] (byte-array (concat (take i b) [(unchecked-byte v)] (drop i b))))
(defn- delete [^bytes b i] (byte-array (concat (take i b) (drop (inc i) b))))
(defn- multi-byte [^bytes b ^java.util.Random r]
  (let [n (alength b) i (+ 4 (.nextInt r (- n 4)))]
    (case (.nextInt r 3)
      0 (reduce (fn [acc _] (substitute acc (+ 4 (.nextInt r (- n 4))) (.nextInt r 256))) b (range (+ 2 (.nextInt r 7))))
      1 (let [len (min (- n i) (inc (.nextInt r 16)))] (byte-array (concat (take (+ i len) b) (take len (drop i b)) (drop (+ i len) b))))
      2 (let [len (min (- n i) (inc (.nextInt r 16)))] (byte-array (concat (take i b) (drop (+ i len) b)))))))

(deftest no-mutation-is-accepted-with-other-claims
  (let [good (binary/pack (shared/encode (plain)))
        n (alength good)
        original (canon (plain))
        expected (canon (:claims (on-test-base (main/check-bundle (plain)))))
        positions (if exhaustive? (range 4 n) (range 4 n (max 1 (quot n 48))))
        r (java.util.Random. 20261016)
        mutants (concat
                 (for [i positions v (range 256) :when (not= v (bit-and 0xff (aget good i)))] [:substitution (substitute good i v)])
                 (for [i positions v (range 256)] [:insertion (insert good i v)])
                 (for [i (range 4 n)] [:deletion (delete good i)])
                 (for [_ (range (if exhaustive? 100000 2000))] [:multi-byte (multi-byte good r)]))
        tally (reduce (fn [t [kind m]] (update t [kind (classify m original expected)] (fnil inc 0))) {} mutants)]
    (println "MUTATION-SWEEP" (if exhaustive? "exhaustive" "sample") (into (sorted-map) tally))
    (is (not-any? (fn [[[_ verdict] _]] (= :OTHER-CLAIMS verdict)) tally) (pr-str tally))
    (is (pos? (reduce + (vals tally))))))

(deftest malformed-files-are-refused
  (let [good (binary/pack (shared/encode (plain)))
        n (alength good)]
    (doseq [[what bad] [["wrong magic" (doto (aclone ^bytes good) (aset-byte 0 (byte 88)))]
                        ["truncated" (java.util.Arrays/copyOf ^bytes good (int (dec n)))]
                        ["trailing bytes" (java.util.Arrays/copyOf ^bytes good (int (inc n)))]
                        ["empty" (byte-array 0)]]]
      (testing what
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"malformed binary bundle" (binary/unpack bad)))))))

(deftest files-are-read-in-either-format
  (let [dir (java.nio.file.Files/createTempDirectory "bundles" (make-array java.nio.file.attribute.FileAttribute 0))
        edn-file (str (.resolve dir "b.edn")) bin-file (str (.resolve dir "b.rbn"))
        s (shared/encode (plain))]
    (main/write-bundle! edn-file s)
    (java.nio.file.Files/write (.toPath (java.io.File. bin-file)) (binary/pack s)
                               ^"[Ljava.nio.file.OpenOption;" (make-array java.nio.file.OpenOption 0))
    (is (= s (main/read-bundle edn-file) (main/read-bundle bin-file)))))

;; ---- regressions from an independent review of the format (2026-10-16) ----------

(defn- varint ^bytes [n]
  (let [out (java.io.ByteArrayOutputStream.)]
    (loop [n (biginteger n)]
      (let [low (.intValue (.and n (biginteger 0x7f))) rest (.shiftRight n 7)]
        (if (zero? (.signum rest)) (.write out (int low)) (do (.write out (int (bit-or low 0x80))) (recur rest)))))
    (.toByteArray out)))
(defn- frame ^bytes [^String text] (let [b (.getBytes text "UTF-8")] (byte-array (concat (varint (alength b)) b))))
(defn- read-varint-at [^bytes data i]
  ;; [value next-position]
  (loop [i i shift 0 v 0]
    (let [b (bit-and 0xff (aget data i)) v (+ v (bit-shift-left (bit-and b 0x7f) shift))]
      (if (zero? (bit-and b 0x80)) [v (inc i)] (recur (inc i) (+ shift 7) v)))))
(defn- edn-of [x] (binding [*print-namespace-maps* false] (pr-str x)))
(defn- refused-promptly? [f]
  (let [r (deref (future (try (f) ::accepted (catch clojure.lang.ExceptionInfo _ ::refused))) 10000 ::hung)]
    (= ::refused r)))

(deftest pack-refuses-malformed-shared-bundles-promptly
  (let [s (shared/encode (plain))
        i (first (keep-indexed (fn [i n] (when (= :bound (first n)) i)) (:terms s)))]
    (doseq [[what bad] [["a negative literal" (assoc-in s [:terms 0] [:nat -1])]
                        ["a negative variable" (assoc-in s [:terms 0] [:bound -1])]
                        ["a forward reference" (assoc-in s [:terms 0] [:app 1 1])]
                        ["a fractional variable" (assoc-in s [:terms i] [:bound 1/2])]
                        ["an extra field" (assoc-in s [:terms i] [:bound 0 :extra])]]]
      (testing what (is (refused-promptly? #(binary/pack bad)))))))

(deftest text-frames-hold-exactly-one-form
  (let [s (shared/encode (plain))
        good (binary/pack s)
        tail (edn-of (dissoc s :terms :constants))
        tail-start (- (alength good) (alength (frame tail)))
        prefix (java.util.Arrays/copyOfRange ^bytes good 0 (int tail-start))]
    (is (= s (binary/unpack (byte-array (concat prefix (frame tail))))) "the reconstruction is faithful")
    (doseq [suffix [" :second-form" " ] this is not valid EDN"]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"malformed binary bundle"
                            (binary/unpack (byte-array (concat prefix (frame (str tail suffix))))))))
    ;; a level frame with trailing text
    (let [[n-constants p] (read-varint-at good 4)
          p (+ p (* 32 n-constants))
          [n-levels p] (read-varint-at good p)]
      (when (pos? n-levels)
        (let [[len q] (read-varint-at good p)
              text (String. (java.util.Arrays/copyOfRange ^bytes good (int q) (int (+ q len))) "UTF-8")
              rebuilt (byte-array (concat (java.util.Arrays/copyOfRange ^bytes good 0 (int p))
                                          (frame (str text " ] this is not EDN"))
                                          (java.util.Arrays/copyOfRange ^bytes good (int (+ q len)) (alength good))))]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"malformed binary bundle" (binary/unpack rebuilt))))))))

(deftest the-body-must-be-a-shared-bundle
  (let [header (byte-array (concat (.getBytes "RBN1" "US-ASCII") (varint 0) (varint 0) (varint 0)))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"malformed binary bundle"
                          (binary/unpack (byte-array (concat header (frame (edn-of (plain))))))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"malformed binary bundle"
                          (binary/unpack (byte-array (concat header (frame (edn-of (assoc (dissoc (shared/encode (plain)) :constants)
                                                                                            :terms []))))))))))

(deftest deep-nesting-is-a-refusal-not-a-crash
  (let [header (byte-array (concat (.getBytes "RBN1" "US-ASCII") (varint 0) (varint 0) (varint 0)))
        deep (str (apply str (repeat 20000 "[")) (apply str (repeat 20000 "]")))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"malformed binary bundle"
                          (binary/unpack (byte-array (concat header (frame deep))))))))
