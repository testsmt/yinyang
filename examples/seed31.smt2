(declare-fun a () String)
(assert (str.< a "ar"))
(assert (= "ar" (str.replace a "ar" "")))
(check-sat)
