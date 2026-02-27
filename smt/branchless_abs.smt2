(set-logic QF_BV)

(declare-const x (_ BitVec 32))

; original abs(x)
(define-fun abs ((x (_ BitVec 32))) (_ BitVec 32) (ite (bvslt x (_ bv0 32)) (bvneg x) x))

; branchless abs(x)
(define-fun xrs () (_ BitVec 32) (bvashr x (_ bv31 32)))
(define-fun abs1 ((x (_ BitVec 32))) (_ BitVec 32) (bvsub (bvxor x xrs) xrs))

(assert (= (abs x) (abs1 x)))

(check-sat)
; sat