(set-logic QF_UF)
(declare-sort U 0)

(declare-fun f (U) U)
(declare-const x U)

(assert (and (= (f (f (f x))) x) (= (f (f (f (f (f x))))) x)))
(assert (distinct (f x) x))

(check-sat)