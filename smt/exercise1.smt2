(set-logic QF_LIA)

(declare-const a Int)
(declare-const b Int)

(assert (= (+ a 10) (* 2 b)))
(assert (= (+ b 20) (* 2 a)))

(check-sat)
; unsat