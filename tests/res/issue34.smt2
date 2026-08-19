(declare-fun x () Int)
(assert (=>
	(= x 3)
	(forall ((x Int)) (let ((?y x))
		(= ?y 3)
	))
))
(check-sat)
