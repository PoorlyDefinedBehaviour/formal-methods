(set-logic QF_NRA)
(set-option :produce-models true)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (= (+ (* x x y) (* y z) (* 2.0 x y z) (* 4.0 x y) (* 8.0 x z) 16.0) 0.0))

(check-sat)
(get-model)