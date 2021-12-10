(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

; test QE reduction for nested floor and LEQ
; FORMULA: floor(floor(floor( -3 x1 + 1 ) + 2) + floor(c1 + 1)) <= 3/2
; -3 < -3 x1 <= 0 ==> -2 < -3 x1 + 1 <= 1 ==> -2 <= floor(-3x1 + 1) <= 1
; ==> 0 <= floor(-3x1 + 1) + 2 <= 3
; ==> 0 <= floor(floor(-3x1 + 1) + 2) <= 3
; ==> floor(c1 + 1) <= floor(floor(-3x1 + 1) + 2) + floor(c1 + 1) <= 3 + floor(c1 + 1)
; hence, floor(c1 + 1) <= 3/2 \/ 1 + floor(c1 + 1) <= 3/2
;        \/ 2 + floor(c1 + 1) <= 3/2 \/ 3 + floor(c1 + 1) <= 3/2
; hence, floor(c1 + 1) <= 3/2, 1/2, -1/2, -3/2.

(assert
 (exists ((|x1| Real) )
    (<=
     (+
      (to_int (+ (to_int (+ (* (+ 3 (- 6)) |x1|) 1))
		 2)
	      )
      (to_int (+ |c1| 1)))
     (/ 3 2))
    ))
