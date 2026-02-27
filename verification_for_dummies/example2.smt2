(declare-const x Int)
(declare-const y Int)

(assert (> x y))
(assert (or (= y (* 2 x)) (= x 11)))
(assert (= 1 (mod y 2)))

(check-sat)
(get-model)