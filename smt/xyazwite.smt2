(set-logic QF_UF)
(set-option :produce-models true)

(declare-sort U 0)

(declare-const b Bool)
(declare-const x U)
(declare-const y U)
(declare-const z U)
(declare-const w U)

(assert (= x (ite b y z)))
(assert (or (= w y) (= w z)))
(assert (distinct x w))

(check-sat)
(get-model)