(ns rainbow.algorithms.reference.net-flow
  "Executable exact-rational net flow / NPV (AHoF). The net balance matches the
  proved Rainbow definition; `npv` discounts a cash-flow stream and `surplus?`
  certifies a nonnegative balance.")

(defn net
  "Net balance of inflow against outflow."
  [inflow outflow]
  (- inflow outflow))

(defn surplus?
  "Whether the balance is nonnegative (inflow at least covers outflow)."
  [inflow outflow]
  (>= (net inflow outflow) 0))

(defn npv
  "Net present value of a cash-flow stream at the given per-period discount
  factor: sum_t cashflow_t * discount^t."
  [cashflows discount]
  (reduce + 0 (map-indexed (fn [t c] (* c (reduce * 1 (repeat t discount))))
                           cashflows)))
