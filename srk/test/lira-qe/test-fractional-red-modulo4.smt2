(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

; test QE reduction for modulo and floor
; -2x + floor(3x - 5/4) \equiv 5/2 mod 3 ==> -2x + floor({ -5/4, -1/4, 3/4, 7/4 }) \equiv 5/2 mod 3
; -2x + {-2, -1, 0, 1} \equiv 5/2 mod 3
; -2x \equiv { 9/2, 7/2, 5/2, 3/2 } mod 3

; Thus: -2x = 1/2 + {-2, -1, 0} /\ 4 \equiv {-2, -1, 0} mod 3
; /\ -2x = 1/2 + {-2, -1, 0} /\ 3 \equiv {-2, -1, 0} mod 3
; /\ -2x = 1/2 + {-2, -1, 0} /\ 2 \equiv {-2, -1, 0} mod 3
; /\ -2x = 1/2 + {-2, -1, 0} /\ 1 \equiv {-2, -1, 0} mod 3

(assert
 (exists ((|x1| Real) )
    (|mod|
     (+ (* (- 2) |x1|)
	(to_int (- (* 3 |x1|) (/ 5 4))))
     (/ 5 2)
     3)
    ))
