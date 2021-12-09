(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

; test QE reduction for modulo
; 2x - floor(3x - 5/2) \equiv 5/2 mod 3 ==> -x \equiv -1/2 mod 3
; -x \equiv -1 mod 3 /\ -1 = -1/2

(assert
 (exists ((|x1| Real) )
    (|mod|
     (+ (* 2 |x1|)
	(- (to_int (+ (* 3 |x1|)
		      (- (/ 5 2)))))
	)
     (/ 5 2)
     3)))
