(ns rainbow.canonical
  "Deterministic, type-tagged serialization for semantic identities."
  (:import (java.nio.charset StandardCharsets)
           (java.security MessageDigest)))

(declare encode)

(defn- write!
  "Appends value's encoding to out; encode is its string."
  [^StringBuilder out value]
  (cond
    (nil? value) (.append out "n;")
    (true? value) (.append out "b1;")
    (false? value) (.append out "b0;")
    (string? value) (-> out (.append "s") (.append (count value)) (.append ":") (.append ^String value))
    (keyword? value) (do (.append out "k") (write! out (namespace value)) (write! out (name value)))
    (symbol? value) (do (.append out "y") (write! out (namespace value)) (write! out (name value)))
    (integer? value) (-> out (.append "i") (.append (str value)) (.append ";"))
    (ratio? value) (-> out (.append "r") (.append (str (numerator value))) (.append "/")
                       (.append (str (denominator value))) (.append ";"))
    (vector? value) (do (.append out "v[") (run! #(write! out %) value) (.append out "]"))
    (list? value) (do (.append out "l(") (run! #(write! out %) value) (.append out ")"))
    ;; a set's elements are written as the (string) encodings of its members, sorted
    (set? value) (do (.append out "e{") (run! #(write! out %) (sort (map encode value))) (.append out "}"))
    (map? value) (do (.append out "m{")
                     (run! (fn [[k v]] (.append out ^String k) (write! out v))
                           (sort-by first (map (fn [[k v]] [(encode k) v]) value)))
                     (.append out "}"))
    :else (throw (ex-info "Unsupported value in canonical serialization"
                          {:error/category :canonical/unsupported-value
                           :value value
                           :class (some-> value class str)}))))

(defn encode
  "Returns a deterministic string. This is a hashing format, not a reader format."
  [value]
  (let [out (StringBuilder.)] (write! out value) (.toString out)))

(defn sha256 [^String value]
  (let [digest (.digest (MessageDigest/getInstance "SHA-256")
                        (.getBytes value StandardCharsets/UTF_8))]
    (str "sha256:" (apply str (map #(format "%02x" (bit-and 0xff %)) digest)))))

(defn content-id [value]
  (sha256 (encode value)))
