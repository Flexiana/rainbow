(ns rainbow.math.rational.signed.lp-equality-price-bridge
  "Untrusted producer of instance-specific equality-price translation evidence.
  Uses supplied actual expanded entries, never substitutes an ideal max split.
  Consumers must independently reconstruct every target and kernel-check all
  four obligations per pair. This is not a verifier or a host execution proof."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.lp-free-price :as price]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- exact-bounded? [x]
  (and (or (integer? x) (ratio? x))
       (<= -10000 (if (ratio? x) (numerator x) x) 10000)
       (<= 1 (if (ratio? x) (denominator x) 1) 10000)))
(defn- require-scalars! [values]
  (when-not (every? exact-bounded? values)
    (throw (ex-info "Expected bounded exact prices before literal encoding"
                    {:error/category :lp-equality-price/invalid-scalar}))))

(defn price-pair-specs
  "Four proof specs for original p and supplied actual pp,pm.
  Construction is not validation: false arithmetic yields proof terms that the
  kernel must reject. Split equality alone does not prove price nonnegativity."
  [original actual-positive actual-negative]
  (require-scalars! [original actual-positive actual-negative])
  (let [[p pp pm] (mapv #'lp/signed-literal [original actual-positive actual-negative])
        split (app 'signed/subtract pp pm)
        same (#'lp/computed-equivalence p split)
        bs [['coefficient lp/signed]]
        contribution
        (app 'signed/equivalent (app 'signed/multiply 'coefficient p)
             (app 'signed/add (app 'signed/multiply 'coefficient pp)
                  (app 'signed/multiply (app 'signed/negate 'coefficient) pm)))]
    (array-map
     :split {:type (app 'signed/equivalent p split) :value same}
     :positive-nonnegative {:type (app 'signed/at-most price/zero pp)
                            :value (#'lp/decided-at-most price/zero pp)}
     :negative-nonnegative {:type (app 'signed/at-most price/zero pm)
                            :value (#'lp/decided-at-most price/zero pm)}
     :universal-contribution
     {:type (f/forall bs contribution)
      :value (f/lam bs (app 'signed/lp-free-price-split-contribution
                            'coefficient p pp pm same))})))

(defn equality-price-specs
  "Produce one four-obligation bundle for each equality's ACTUAL appended pair.
  base-row-count identifies the untouched inequality prefix; exact expanded
  vector length is required. Prefix values are bounded but not proved unchanged.
  Empty equality lists return no obligations, not a complete certificate verdict.
  The caller supplies original free prices and actual standardizer output; this
  producer does not attest their provenance or correspondence to row arrays."
  [original-free-prices actual-expanded-prices base-row-count]
  (when-not (and (vector? original-free-prices) (vector? actual-expanded-prices)
                 (integer? base-row-count) (<= 0 base-row-count 32)
                 (<= (count actual-expanded-prices) 32)
                 (= (count actual-expanded-prices)
                    (+ base-row-count (* 2 (count original-free-prices)))))
    (throw (ex-info "Expected exact expanded price-vector shape, at most 32 rows"
                    {:error/category :lp-equality-price/table-shape})))
  (require-scalars! (concat original-free-prices actual-expanded-prices))
  (mapv (fn [i]
          (let [j (+ base-row-count (* 2 i))]
            {:equality-index i :expanded-row-indices [j (inc j)]
             :specs (price-pair-specs (nth original-free-prices i)
                                      (nth actual-expanded-prices j)
                                      (nth actual-expanded-prices (inc j)))}))
        (range (count original-free-prices))))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-free-price rainbow.math.rational.signed.decide-order])

(defn install
  "Adds this module's own declarations."
  [env]
  env)

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-equality-price-bridge))
