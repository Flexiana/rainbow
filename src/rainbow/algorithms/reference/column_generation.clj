(ns rainbow.algorithms.reference.column-generation
  "Executable column-generation pricing, matching the proved Rainbow
  definition.")

(defn worth-adding?
  "True iff a column's dual value covers its cost (negative reduced cost)."
  [cost dual]
  (<= cost dual))

(defn price-columns
  "Columns worth adding, from [cost dual] candidate pairs."
  [candidates]
  (filter (fn [[cost dual]] (worth-adding? cost dual)) candidates))

(defn optimal?
  "The master is optimal when no candidate column prices favorably."
  [candidates]
  (empty? (price-columns candidates)))
