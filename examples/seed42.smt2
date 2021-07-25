(declare-fun a () Real)
(declare-fun b () Real)
(assert (= b (+ 1 (* a a (+ 1 (/ b b))))))
(check-sat)
