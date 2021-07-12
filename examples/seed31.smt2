(declare-fun a () String)
(assert (str.< a "ar"))
(assert (= "ar" ""))
(check-sat)
