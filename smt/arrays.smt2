(set-logic QF_AX)

(declare-sort I 0)
(declare-sort E 0)

(declare-fun i () I)
(declare-fun j () I)
(declare-fun tmp () E)
(declare-fun a_in () (Array I E))
(declare-fun a_out () (Array I E))

(assert (= tmp (select a_in i)))
(assert (= a_out (store 
                    (store a_in i (select a_in j))
                    j tmp)))
                  
(assert (= (select a_in i) (select a_in j)))
(assert (distinct a_in a_out))

(check-sat)