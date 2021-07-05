from src.parsing.parse import *
script_str="""\
(declare-fun ?v_0 () Int)
(assert (let ((?v_0 (+ (* 4 f3) 1))) (= ?v_0 0)))
(check-sat)
(exit)
"""
script,_ = parse_str(script_str, silent=False)

