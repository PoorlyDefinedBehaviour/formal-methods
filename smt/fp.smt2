(set-logic QF_FP)
(set-option :produce-models true)

(declare-const a Float32)
(declare-const b Float32)
(declare-const c Float32)
(declare-const rm RoundingMode)

(assert (distinct (fp.fma rm a b c) (fp.add rm (fp.mul rm a b) c)))

(check-sat)
(get-model)
(get-value ((fp.fma rm a b c)))
(get-value ((fp.add rm (fp.mul rm a b) c)))

