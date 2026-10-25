(ns rainbow.canonical-stream
  "Untrusted streaming identity encoding for reuse; kernel paths use rainbow.canonical."
  (:require [rainbow.canonical :as canonical])
  (:import (java.io BufferedWriter OutputStream OutputStreamWriter Writer)
           (java.nio.charset StandardCharsets)
           (java.security DigestOutputStream MessageDigest)))

(defn- write-incrementally!
  [^Writer out value]
  (letfn [(put [^String s] (.write out s))
          (emit [v] (write-incrementally! out v))]
    (cond
      (string? value) (do (put (str "s" (count value) ":")) (put value))
      (vector? value) (do (put "v[") (run! emit value) (put "]"))
      (list? value) (do (put "l(") (run! emit value) (put ")"))
      ;; Legacy sets encode the sorted member encodings AS STRINGS. Map keys
      ;; instead contribute their encodings directly. Preserve that distinction.
      (set? value) (do (put "e{") (run! emit (sort (map canonical/encode value))) (put "}"))
      (map? value) (do (put "m{")
                       (doseq [[key v] (sort-by first (map (fn [[k v]] [(canonical/encode k) v]) value))]
                         (put key) (emit v))
                       (put "}"))
      :else (put (canonical/encode value)))))

(defn content-id-incremental
  "Hashes the existing canonical encoding without constructing its whole string
  or UTF-8 byte array. IDs are identical to content-id, including UTF-16 string
  lengths and sorted encoded map keys/set members. Sorting still materializes
  those keys/members; ordinary vector/list values stream through a fixed buffer.
  The legacy rainbow.canonical/content-id entry point remains unchanged."
  [value]
  (let [digest (MessageDigest/getInstance "SHA-256")]
    ;; One persistent UTF-8 encoder preserves surrogate handling across writes.
    ;; Closing, rather than just flushing, also finishes a trailing surrogate.
    (with-open [out (BufferedWriter.
                    (OutputStreamWriter.
                     (DigestOutputStream. (OutputStream/nullOutputStream) digest)
                     StandardCharsets/UTF_8))]
      (write-incrementally! out value))
    (str "sha256:" (apply str (map #(format "%02x" (bit-and 0xff %)) (.digest digest))))))
