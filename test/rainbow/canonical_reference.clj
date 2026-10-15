(ns rainbow.canonical-reference
  "Deterministic, type-tagged serialization for semantic identities."
  (:import (java.nio.charset StandardCharsets)
           (java.security MessageDigest)))

(declare encode)

(defn- encode-seq [tag open close xs]
  (str tag open (apply str (map encode xs)) close))

(defn encode
  "Returns a deterministic string. This is a hashing format, not a reader format."
  [value]
  (cond
    (nil? value) "n;"
    (true? value) "b1;"
    (false? value) "b0;"
    (string? value) (str "s" (count value) ":" value)
    (keyword? value) (str "k" (encode (namespace value)) (encode (name value)))
    (symbol? value) (str "y" (encode (namespace value)) (encode (name value)))
    (integer? value) (str "i" value ";")
    (ratio? value) (str "r" (numerator value) "/" (denominator value) ";")
    (vector? value) (encode-seq "v" "[" "]" value)
    (list? value) (encode-seq "l" "(" ")" value)
    (set? value) (encode-seq "e" "{" "}" (sort (map encode value)))
    (map? value) (let [entries (sort-by (comp encode key) value)]
                   (str "m{" (apply str (map (fn [[k v]]
                                                (str (encode k) (encode v)))
                                              entries)) "}"))
    :else (throw (ex-info "Unsupported value in canonical serialization"
                          {:error/category :canonical/unsupported-value
                           :value value
                           :class (some-> value class str)}))))

(defn sha256 [^String value]
  (let [digest (.digest (MessageDigest/getInstance "SHA-256")
                        (.getBytes value StandardCharsets/UTF_8))]
    (str "sha256:" (apply str (map #(format "%02x" (bit-and 0xff %)) digest)))))

(defn content-id [value]
  (sha256 (encode value)))
