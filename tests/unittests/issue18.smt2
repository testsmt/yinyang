(declare-fun a () String)
(declare-fun b () String)
(assert (= a b))                                                                 
(check-sat)
(simplify (= a b))                                                                 
(simplify (str.++ a b))
(assert (= a b))                                                                 
(check-sat)
(get-model)