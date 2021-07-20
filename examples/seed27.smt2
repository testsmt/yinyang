(declare-fun x () String)                                                       
(assert (> (- (str.to_int (str.++ x x))) 0))
(check-sat)
