(set-logic QF_DTLIA)
(set-option :produce-models true)

(declare-datatypes ((Tree 0))
  ((
    (node (data Int) (left Tree) (right Tree)) 
    (nil)
  ))
)

(declare-fun x () Tree)
(declare-fun y () Tree)

(assert ((_ is node) x))
(assert ((_ is node) y))

(assert (= (left x) (right y)))
(assert (> (data x) 100))

(check-sat)
(get-model)