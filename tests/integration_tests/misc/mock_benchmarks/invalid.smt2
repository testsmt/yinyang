(declare-fun x () Int)
(declare-fun w () Bool)
(assert (= x (- 1
(assert (= w (= x (- 1))))
(assert w)
(check-sat)
