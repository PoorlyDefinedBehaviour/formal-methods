(set-logic QF_BV)
(set-option :produce-models true)

(declare-const x (_ BitVec 8))

(assert (= (bvmul x (_ bv5 8)) (_ bv1 8)))

(check-sat)
(get-model)