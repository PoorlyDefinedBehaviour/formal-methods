(set-logic QF_BV)

(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))

(assert (= x (bvmul z (_ bv2 32))))
(assert (= (bvmul x y) (_ bv1 32)))

(checks-sat)