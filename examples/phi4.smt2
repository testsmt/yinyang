; phi4
(declare-fun y () Real)
(declare-fun w () Real)
(declare-fun v () Real)
(assert (and (< y v) (>= w v)  
             (< (/ w v) 0)  (> y 0)))
(check-sat)
