(set-logic UF)

(declare-sort S 0)
(declare-fun Human (S) Bool)
(declare-fun Mortal (S) Bool)
(declare-const Socrates S)

(assert (forall ((x S)) (=> (Human x) (Mortal x))))
(assert (Human Socrates))
(assert (not (Mortal Socrates)))
; (assert (Mortal Socrates))

(check-sat)