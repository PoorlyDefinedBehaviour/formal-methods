(set-logic QF_SLIA)
(set-option :produce-models true)

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)
(declare-const p4 Bool)
(declare-const p5 Bool)
(declare-const p6 Bool)
(declare-const p7 Bool)
(declare-const p8 Bool)
(declare-const p9 Bool)
(declare-const p10 Bool)
(declare-const p11 Bool)
(declare-const p12 Bool)


(declare-const x1 String)
(declare-const x2 String)
(declare-const x3 String)
(declare-const x4 String)
(declare-const x5 String)

(declare-const i1 String)
(declare-const i2 String)
(declare-const i3 String)
(declare-const i4 String)
(declare-const i5 String)
(declare-const i6 String)

(define-const result String "abbaabb")

(assert (and (<= (str.len x1) 2) (<= (str.len x2) 2)))

(assert (= i1 (ite p1 x1 x2)))
(assert (= i2 (ite p2 x1 x2)))
(assert (= x3 (str.++ i1 i2)))

(assert (= i3 (ite p3 x1 (ite p4 x2 x3))))
(assert (= i4 (ite p5 x1 (ite p6 x2 x3))))
(assert (= x4 (str.++ i3 i4)))

(assert (= i5 (ite p7 x1 (ite p8 x2 (ite p9 x3 x4)))))
(assert (= i6 (ite p10 x1 (ite p11 x2 (ite p12 x3 x4)))))
(assert (= x5 (str.++ i5 i6)))

(assert (= x5 result))

(check-sat)
(get-model)