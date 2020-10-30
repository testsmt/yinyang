; phi3
(declare-fun x () Real)
(assert (not (= (+ (+ 1.0 x) 6.0) (+ 7.0 x))))
(check-sat)
