(ns rainbow.or.lp-certificate-wire
  "Bounded restricted-EDN transport for LP proof VALUES, never executable code.
  Decode/encode are not verification. Replay uses the receiver's own request,
  claim, epsilon and checked environment. Size guards are not process isolation."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.or.lp-original-plan-verifier :as verifier])
  (:import (java.io PushbackReader StringReader)
           (java.nio.charset StandardCharsets)))

(def format-id :rainbow.lp/proof-values-v1)
(def limits {:max-bytes 4194304 :max-depth 256 :max-nodes 250000 :max-token-chars 256
             :max-expansion-depth 512})
(defn- refuse! [category message] (throw (ex-info message {:error/category category})))
(defn- limit! [condition] (when-not condition (refuse! :lp-wire/size "Wire data exceeds a fixed size limit")))
(defn- syntax! [] (refuse! :lp-wire/syntax "Unsupported or malformed restricted EDN"))

(defn- preflight! [text]
  ;; Scan iteratively BEFORE the recursive EDN reader. Dispatch, metadata,
  ;; quoting, character and list forms are excluded, including discard forms
  ;; whose contents would otherwise disappear before a post-parse depth check.
  (when-not (string? text) (refuse! :lp-wire/input "Expected an EDN string"))
  (limit! (<= (count text) (:max-bytes limits)))
  (let [bytes (alength (.getBytes ^String text StandardCharsets/UTF_8)) n (count text)]
    (limit! (<= bytes (:max-bytes limits)))
    (loop [i 0 stack [] mode :normal escape? false token? false width 0 nodes 0 peak 0]
      (limit! (and (<= width (:max-token-chars limits)) (<= nodes (:max-nodes limits))
                   (<= (count stack) (:max-depth limits))))
      (if (= i n)
        (do (when (or (= mode :string) (seq stack)) (syntax!))
            {:bytes bytes :nodes nodes :depth peak})
        (let [c (.charAt ^String text i)]
          (cond
            (= mode :comment)
            (recur (inc i) stack (if (or (= c \newline) (= c \return)) :normal :comment)
                   false false 0 nodes peak)

            (= mode :string)
            (cond escape? (recur (inc i) stack :string false false (inc width) nodes peak)
                  (= c \\) (recur (inc i) stack :string true false (inc width) nodes peak)
                  (= c \") (recur (inc i) stack :normal false false 0 nodes peak)
                  :else (recur (inc i) stack :string false false (inc width) nodes peak))

            (= c \;) (recur (inc i) stack :comment false false 0 nodes peak)
            (or (Character/isWhitespace c) (= c \,))
            (recur (inc i) stack :normal false false 0 nodes peak)
            (= c \") (recur (inc i) stack :string false false 0 (inc nodes) peak)
            (contains? #{\# \^ \\ \@ \` \~ \' \( \)} c) (syntax!)
            (or (= c \[) (= c \{))
            (let [s (conj stack (if (= c \[) \] \}))]
              (recur (inc i) s :normal false false 0 (inc nodes) (max peak (count s))))
            (or (= c \]) (= c \}))
            (do (when-not (= c (peek stack)) (syntax!))
                (recur (inc i) (pop stack) :normal false false 0 nodes peak))
            :else (recur (inc i) stack :normal false true (if token? (inc width) 1)
                         (if token? nodes (inc nodes)) peak)))))))

(defn- scalar? [x]
  (or (nil? x) (boolean? x) (keyword? x) (symbol? x) (string? x)
      (and (integer? x) (<= Long/MIN_VALUE x Long/MAX_VALUE))
      (and (ratio? x) (<= Long/MIN_VALUE (numerator x) Long/MAX_VALUE)
           (<= 1 (denominator x) Long/MAX_VALUE))))
(defn- bounded-tree! [data]
  ;; Also protects the encoder from hostile in-memory nesting/lazy collections.
  (loop [pending [[data 0]] nodes 0]
    (when-let [[v depth] (peek pending)]
      (limit! (and (< nodes (:max-nodes limits)) (<= depth (:max-depth limits))))
      (let [pending (pop pending)]
        (cond
          (or (map? v) (vector? v))
          (let [size (if (map? v) (* 2 (count v)) (count v))
                children (if (map? v) (mapcat identity v) v)]
            (limit! (<= (+ nodes (count pending) size 1) (:max-nodes limits)))
            (recur (into pending (map #(vector % (inc depth))) children) (inc nodes)))
          (scalar? v)
          (do (when (or (string? v) (symbol? v) (keyword? v))
                (limit! (<= (count (str v)) (:max-token-chars limits))))
              (recur pending (inc nodes)))
          :else (refuse! :lp-wire/value "Only maps, vectors and bounded EDN scalars are supported"))))))

(defn- obligations [claim]
  (case claim :feasible-report verifier/report-obligations
              :optimal-plan verifier/optimality-obligations
              :epsilon-plan verifier/epsilon-obligations nil))
(defn- expansion-depth! [proofs]
  ;; A flat binder/argument vector can elaborate into a deep core term even
  ;; when the EDN itself is shallow. Charge all children the maximum expansion
  ;; of each surface form; conservative overestimates intentionally refuse.
  (loop [pending (mapv #(vector % 0) (vals proofs))]
    (when-let [[v depth] (peek pending)]
      (let [width (if (vector? v)
                    (case (first v)
                      (:fn :forall) (if (vector? (second v)) (inc (count (second v))) 1)
                      (:app :->) (count v)
                      1) 1)
            depth (+ depth width)
            children (cond (vector? v) v (map? v) (mapcat identity v) :else [])]
        (limit! (<= depth (:max-expansion-depth limits)))
        (recur (into (pop pending) (map #(vector % depth)) children))))))
(defn- envelope! [packet]
  (let [claim (:claim packet) required (obligations claim)
        fields (cond-> #{:format :claim :request/id :proofs} (= claim :epsilon-plan) (conj :epsilon))]
    (when-not (and (map? packet) required (= fields (set (keys packet)))
                   (= format-id (:format packet))
                   (string? (:request/id packet)) (re-matches #"sha256:[0-9a-f]{64}" (:request/id packet))
                   (map? (:proofs packet)) (= (set required) (set (keys (:proofs packet)))))
      (refuse! :lp-wire/envelope "Invalid version, fields, claim, request ID or proof coverage"))
    (when (= claim :epsilon-plan)
      (let [e (:epsilon packet)]
        (when-not (and (or (integer? e) (ratio? e)) (<= 0 e)
                       (<= (if (ratio? e) (numerator e) e) 10000)
                       (<= 1 (if (ratio? e) (denominator e) 1) 10000))
          (refuse! :lp-wire/envelope "Invalid epsilon in envelope"))))
    (expansion-depth! (:proofs packet))
    packet))

(defn decode
  "Read exactly one bounded envelope. Does NOT check mathematical proofs.
  Tags, eval, discard, metadata, quoting, character/list/set forms are excluded.
  Throws a categorized ExceptionInfo on invalid wire data."
  [text]
  (preflight! text)
  (let [packet
        (try
          (with-open [reader (PushbackReader. (StringReader. text))]
            (let [end (Object.) options {:eof end :readers {} :default (fn [& _] (syntax!))}
                  value (edn/read options reader)]
              (when (or (identical? end value) (not (identical? end (edn/read options reader)))) (syntax!))
              value))
          (catch clojure.lang.ExceptionInfo e (throw e))
          (catch RuntimeException _ (syntax!)))]
    (bounded-tree! packet)
    (envelope! packet)))

(defn- ordered [data]
  (cond (map? data) (into (sorted-map-by #(compare (canonical/encode %1) (canonical/encode %2)))
                         (map (fn [[k v]] [k (ordered v)])) data)
        (vector? data) (mapv ordered data)
        :else data))

(defn encode
  "Serialize untrusted proof values for a validated request; never certifies them.
  Printing is deterministic and independent of ambient print limits. No problem
  data, environment, producer target types or solver status are transported."
  ([original actual report proofs] (encode original actual report proofs {}))
  ([original actual report proofs options]
   (let [id (verifier/request-id original actual report options)
         claim (get options :claim :feasible-report)
         packet (cond-> {:format format-id :claim claim :request/id id :proofs proofs}
                  (= claim :epsilon-plan) (assoc :epsilon (:epsilon options)))]
     (bounded-tree! packet)
     (envelope! packet)
     (let [text (binding [*print-length* nil *print-level* nil *print-meta* false
                         *print-dup* false *print-readably* true *print-namespace-maps* false]
                  (pr-str (ordered packet)))]
       ;; Reject EDN-ambiguous symbol spellings or any lossy representation.
       (when-not (= packet (decode text)) (refuse! :lp-wire/roundtrip "Envelope did not round-trip exactly"))
       text))))

(defn replay
  "Replay an envelope against the RECEIVER's own data/options and checked env.
  Matching metadata/hashes is only an early guard: every proof is still checked.
  Producer-supplied resource settings/environment/targets are never accepted.
  Does not supply authentication, privacy, process isolation or a Level-6 claim."
  ([env original actual report text] (replay env original actual report text {}))
  ([env original actual report text options]
   (try
     (let [packet (decode text) id (verifier/request-id original actual report options)
           claim (get options :claim :feasible-report)]
       (when-not (and (= claim (:claim packet)) (= id (:request/id packet))
                      (or (not= claim :epsilon-plan) (= (:epsilon options) (:epsilon packet))))
         (refuse! :lp-wire/request-mismatch "Envelope does not match the receiver's request/claim"))
       (let [result (verifier/verify env original actual report (:proofs packet) options)]
         (if (contains? #{:original-plan-report-verified :original-plan-optimal :original-plan-epsilon-verified}
                        (:status result))
           (assoc result :certificate/id (canonical/content-id packet))
           result)))
     (catch clojure.lang.ExceptionInfo e
       {:status :refused :error/category (or (:error/category (ex-data e)) :lp-wire/exception)})
     (catch IllegalArgumentException _ {:status :refused :error/category :lp-wire/input}))))
