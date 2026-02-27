(set-logic QF_FP)
(set-option :produce-models true)

(declare-const a Float32)
(declare-const b Float32)
(declare-const c Float32)
(declare-const rm RoundingMode)

; a + (b + c) != (a + b) c
(assert (= rm roundTowardNegative))
(assert (= (fp.add rm a (fp.add rm b c)) 
           (fp.add rm (fp.add rm a b) c)))

(check-sat)
(get-model)