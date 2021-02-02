; Bug hidden by = -> distinct
(declare-fun a () Int)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (> a 0))
(assert (distinct (* (/ b b) c) 2.0))
(check-sat)
(check-sat)
(get-model)
