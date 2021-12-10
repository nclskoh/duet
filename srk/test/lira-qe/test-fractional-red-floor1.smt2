(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

; test QE reduction for floor + <=
; {0, 1, 2, 3, 4} <= 3/2 ==> 0 <= {3/2, 1/2, -1/2, -3/2, -5/2}
; algorithm gives an extra term which is unnecessary in this case
; but may be needed in other cases.

(assert
 (exists ((|x1| Real) ) (<= (to_int (* 5 |x1|)) (/ 3 2) )))

; Solve
(check-sat)
(get-model)
