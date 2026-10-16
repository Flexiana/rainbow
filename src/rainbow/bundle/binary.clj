(ns rainbow.bundle.binary
  "A binary file format for shared proof bundles (rainbow.bundle.shared, schema 3).

  The shared encoding already writes every distinct subterm and every constant once;
  as EDN text each node still costs about sixteen bytes and each constant seventy-one.
  This format writes the same schema-3 bundle with a one-byte tag per node, children
  as variable-length back references (usually one byte), constants as their raw
  32-byte hashes, and universe levels once each. Everything that is not term data
  (claims, base, ids, metadata) stays EDN.

  It is only an encoding: `unpack` gives back exactly the schema-3 map `pack` was
  given, which `rainbow.bundle.shared/decode` turns into the plain bundle, and the
  kernel then checks that as it checks any other. Nothing here is trusted. The
  unpacker refuses anything malformed (wrong magic, a truncated or overlong file, a
  back reference that is zero or reaches past the first node, an index out of range,
  an unknown tag); what it accepts still has every declaration's id recomputed by
  the kernel.

  Layout (all integers unsigned LEB128):
    \"RBN1\"
    constant count, then 32 bytes each (the hash after \"sha256:\")
    level count, then each level as length-prefixed EDN text
    node count, then each node: tag byte, fields
      0 sort  level        1 bound  index        2 nat  value
      3 const constant, level count, levels
      4 app   f a          5 lam / 6 pi  domain body mode(0 explicit, 1 implicit)
      7 let   type value body
      (f, a, domain, body, ... are written as  node position - child position)
    length-prefixed EDN text: the schema-3 map without :terms and :constants"
  (:require [clojure.edn :as edn]
            [rainbow.bundle.shared :as shared])
  (:import (java.io ByteArrayOutputStream)))

(def magic (.getBytes "RBN1" "US-ASCII"))

(defn binary? [^bytes data]
  (and (>= (alength data) 4) (java.util.Arrays/equals (java.util.Arrays/copyOfRange data 0 4) ^bytes magic)))

;; ---------------------------------------------------------------- writing

(defn- write-varint [^ByteArrayOutputStream out n]
  (when-not (and (integer? n) (not (neg? n)))
    (throw (ex-info "binary bundles hold non-negative integers only" {:value n :error/category :bundle/malformed-binary})))
  (loop [n (biginteger n)]
    (let [low (.intValue (.and n (biginteger 0x7f)))
          rest (.shiftRight n 7)]
      (if (zero? (.signum rest))
        (.write out (int low))
        (do (.write out (int (bit-or low 0x80))) (recur rest))))))

(defn- write-text [^ByteArrayOutputStream out ^String s]
  (let [b (.getBytes s "UTF-8")] (write-varint out (alength b)) (.write out b 0 (alength b))))

(defn- hash-bytes [^String id]
  (when-not (re-matches #"sha256:[0-9a-f]{64}" id)
    (throw (ex-info "binary bundles carry sha256 content ids only" {:id id})))
  (let [hex (subs id 7)]
    (byte-array (for [i (range 0 64 2)] (unchecked-byte (Integer/parseInt (subs hex i (+ i 2)) 16))))))

(defn- edn-text [x]
  (binding [*print-namespace-maps* false *print-length* nil *print-level* nil
            *print-meta* false *print-dup* false *print-readably* true]
    (pr-str x)))

(def ^:private tags {:sort 0 :bound 1 :nat 2 :const 3 :app 4 :lam 5 :pi 6 :let 7})
(def ^:private modes {:explicit 0 :implicit 1})

(defn pack
  "The bytes of a schema-3 (shared) bundle."
  ^bytes [shared-bundle]
  (when-not (= 3 (:rainbow.bundle/schema-version shared-bundle))
    (throw (ex-info "pack takes a shared (schema 3) bundle" {})))
  ;; Validate the whole shared representation first (node shapes, field types,
  ;; strictly backward references, index ranges): malformed input is refused,
  ;; never coerced into a different, valid bundle.
  (shared/decode shared-bundle)
  (let [out (ByteArrayOutputStream.)
        nodes (:terms shared-bundle)
        levels (vec (distinct (mapcat (fn [n] (case (first n) :sort [(second n)] :const (nth n 2) [])) nodes)))
        level-index (zipmap levels (range))]
    (.write out ^bytes magic 0 4)
    (write-varint out (count (:constants shared-bundle)))
    (doseq [id (:constants shared-bundle)] (.write out ^bytes (hash-bytes id) 0 32))
    (write-varint out (count levels))
    (doseq [l levels] (write-text out (edn-text l)))
    (write-varint out (count nodes))
    (doseq [[i n] (map-indexed vector nodes)]
      (let [back #(write-varint out (- i %))]
        (.write out (int (tags (first n))))
        (case (first n)
          :sort (write-varint out (level-index (second n)))
          :bound (write-varint out (second n))
          :nat (write-varint out (second n))
          :const (do (write-varint out (second n))
                     (write-varint out (count (nth n 2)))
                     (doseq [l (nth n 2)] (write-varint out (level-index l))))
          :app (do (back (nth n 1)) (back (nth n 2)))
          (:lam :pi) (do (back (nth n 1)) (back (nth n 2)) (.write out (int (modes (nth n 3)))))
          :let (do (back (nth n 1)) (back (nth n 2)) (back (nth n 3))))))
    (write-text out (edn-text (dissoc shared-bundle :terms :constants)))
    (.toByteArray out)))

;; ---------------------------------------------------------------- reading

(defn- refuse! [message data]
  (throw (ex-info (str "malformed binary bundle: " message) (assoc data :error/category :bundle/malformed-binary))))

(defn- reader [^bytes data]
  (let [position (volatile! 4)]
    {:byte (fn []
             (when (>= @position (alength data)) (refuse! "truncated" {:at @position}))
             (let [b (bit-and 0xff (aget data @position))] (vswap! position inc) b))
     :bytes (fn [n]
              (when (> (+ @position n) (alength data)) (refuse! "truncated" {:at @position}))
              (let [b (java.util.Arrays/copyOfRange data (int @position) (int (+ @position n)))] (vswap! position + n) b))
     :done? (fn [] (= @position (alength data)))}))

(defn- read-varint
  "A LEB128 integer; at most max-bytes long (an index), or unbounded (a literal)."
  [{:keys [byte]} max-bytes]
  (loop [result (biginteger 0) shift 0 used 0]
    (when (and max-bytes (>= used max-bytes)) (refuse! "an integer is too long" {}))
    (let [b (byte)
          result (.or result (.shiftLeft (biginteger (bit-and b 0x7f)) shift))]
      (if (zero? (bit-and b 0x80))
        (if (< (.bitLength result) 63) (long result) (bigint result))
        (recur result (+ shift 7) (inc used))))))

(defn- read-index [r] (read-varint r 9))

(defn- read-text [r]
  (let [n (read-index r)] (String. ^bytes ((:bytes r) n) "UTF-8")))

(defn- read-one-form
  "The single EDN value in a frame: anything after it but whitespace is refused."
  [^String text]
  (with-open [in (java.io.PushbackReader. (java.io.StringReader. text))]
    (let [eof (Object.)
          value (edn/read {:eof eof} in)]
      (when (identical? eof value) (refuse! "an empty text frame" {}))
      (when-not (identical? eof (edn/read {:eof eof} in)) (refuse! "more than one form in a text frame" {}))
      value)))

(defn- hex [^bytes b] (apply str (map #(format "%02x" (bit-and 0xff %)) b)))

(declare unpack*)

(defn unpack
  "The schema-3 bundle in bytes written by pack. Refuses anything malformed, with an
  ex-info whatever went wrong while reading."
  [^bytes data]
  (try (unpack* data)
       (catch clojure.lang.ExceptionInfo e (throw e))
       (catch Exception e (refuse! (str "unreadable (" (.getMessage e) ")") {}))
       ;; a text frame nested deeply enough to exhaust the reader's stack
       (catch StackOverflowError _ (refuse! "a text frame is nested too deeply" {}))))

(defn- unpack* [^bytes data]
  (when-not (binary? data) (refuse! "not a binary bundle (magic)" {}))
  (let [r (reader data)
        constants (vec (repeatedly (read-index r) #(str "sha256:" (hex ((:bytes r) 32)))))
        levels (vec (repeatedly (read-index r) #(read-one-form (read-text r))))
        level (fn [] (let [k (read-index r)] (when-not (< k (count levels)) (refuse! "level out of range" {:level k})) (nth levels k)))
        node-count (read-index r)
        nodes (loop [i 0 nodes (transient [])]
                (if (= i node-count)
                  (persistent! nodes)
                  (let [child (fn [] (let [d (read-index r)]
                                       (when-not (<= 1 d i) (refuse! "a child is not an earlier node" {:node i :back d}))
                                       (- i d)))
                        mode (fn [] (case ((:byte r)) 0 :explicit 1 :implicit (refuse! "unknown binder mode" {:node i})))
                        tag ((:byte r))
                        node (case tag
                               0 [:sort (level)]
                               1 [:bound (read-index r)]
                               2 [:nat (read-varint r nil)]
                               3 (let [k (read-index r)]
                                   (when-not (< k (count constants)) (refuse! "constant out of range" {:node i}))
                                   [:const k (vec (repeatedly (read-index r) level))])
                               4 (let [f (child) a (child)] [:app f a])
                               (5 6) (let [d (child) b (child)] [(if (= 5 tag) :lam :pi) d b (mode)])
                               7 (let [t (child) v (child) b (child)] [:let t v b])
                               (refuse! "unknown node tag" {:node i :tag tag}))]
                    (recur (inc i) (conj! nodes node)))))
        rest (read-one-form (read-text r))]
    (when-not ((:done? r)) (refuse! "bytes after the end" {}))
    (when-not (map? rest) (refuse! "the bundle body is not a map" {}))
    (when-not (and (= 3 (:rainbow.bundle/schema-version rest)) (#{1 2} (:rainbow.bundle/payload-schema rest)))
      (refuse! "the body is not a shared (schema 3) bundle" {}))
    (when (or (contains? rest :terms) (contains? rest :constants))
      (refuse! "the body repeats the node or constant table" {}))
    (assoc rest :constants constants :terms nodes)))
