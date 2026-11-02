(ns rainbow.or.lp-min-long-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.or.lp-certificate :as lp]))

(defn nnrat [n] [:app [:const 'nnrat/make []] [:nat n] [:nat 0]])

(deftest minimum-long-coefficient-encodes-its-exact-magnitude
  (is (= [:app [:const 'signed/make []] (nnrat 0) (nnrat 9223372036854775808N)]
         (#'lp/signed-literal Long/MIN_VALUE))))

(deftest ordinary-coefficients-retain-their-encoding
  (is (= [:app [:const 'signed/make []] (nnrat 0) (nnrat 7)]
         (#'lp/signed-literal -7)))
  (is (= [:app [:const 'signed/make []] (nnrat 7) (nnrat 0)]
         (#'lp/signed-literal 7))))
