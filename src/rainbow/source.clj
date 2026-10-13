(ns rainbow.source
  "Where the Clojure source of this process lives, read from the classpath.

  Tools that read source files (line counts, alias indexes, `ns`-to-file checks)
  used to assume one tree at the relative path `src/`. Rainbow Pro runs with two
  source trees -- its own `src` and the open core's `../rainbow/src` -- so a fixed
  path silently saw only half the code. The roots are now every classpath
  directory named `src`, in classpath order; the open core alone has one."
  (:require [clojure.java.io :as io]
            [clojure.string :as string]))

(defn roots
  "Source root directories, in classpath order. Falls back to `src` when the
  classpath names none (a REPL started some other way)."
  []
  (let [found (->> (string/split (or (System/getProperty "java.class.path") "")
                                 (re-pattern java.io.File/pathSeparator))
                   (map io/file)
                   (filter #(and (.isDirectory ^java.io.File %) (= "src" (.getName ^java.io.File %))))
                   distinct
                   vec)]
    (if (seq found) found [(io/file "src")])))

(defn clj-files
  "Every .clj file under `relative-dir` (e.g. \"rainbow\") in every source root."
  [relative-dir]
  (->> (roots)
       (mapcat #(file-seq (io/file % relative-dir)))
       (filter #(string/ends-with? (.getName ^java.io.File %) ".clj"))))

(defn file
  "Resolves a repository path such as \"src/rainbow/kernel.clj\" against the
  source roots: the first root that has it, else the path as given (so a missing
  file still fails loudly where it is read)."
  [path]
  (let [relative (string/replace-first (str path) #"^src/" "")]
    (or (some #(let [f (io/file % relative)] (when (.exists f) f)) (roots))
        (io/file (str path)))))

(defn repo-path
  "A source file's repository-relative path, \"src/rainbow/...\", whichever root it
  was found under -- so path-prefix rules (Gate F's corpus prefixes) classify a
  file from either tree the same way."
  [f]
  (let [path (.getCanonicalPath (io/file f))]
    (or (some (fn [root]
                (let [r (str (.getCanonicalPath ^java.io.File root) java.io.File/separator)]
                  (when (string/starts-with? path r)
                    (str "src/" (subs path (count r))))))
              (roots))
        (str f))))
