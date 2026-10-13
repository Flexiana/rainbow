(ns rainbow.algorithms.reference.svm
  "Executable linear SVM classification, matching the proved margin rule.")

(defn classify-positive? [margin threshold] (<= threshold margin))

(defn classify
  "SVM label (+1/-1) for weights, bias, input x via the decision boundary."
  [weights bias x]
  (let [margin (- (reduce + (map * weights x)) bias)]
    (if (classify-positive? margin 0) 1 -1)))

(defn support-vector?
  "A training point is a support vector when its functional margin equals 1
  (lies exactly on the margin boundary)."
  [weights bias x y]
  (= 1 (* y (- (reduce + (map * weights x)) bias))))
