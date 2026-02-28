(define-fun add_1 ( (n Int)) Int
  (+ n 1))

(define-fun is_even ( (n Int)) Bool
  (= 0 (mod n 2)))

(declare-const n Int)

(assert (is_even (add_1 n)))

; Is there an `n` such that `n + 1` is even?
(check-sat)
(get-model)