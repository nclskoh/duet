(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

; test QE reduction for nested floor and <
; FORMULA: floor(floor( -3 x1 + 1 ) + 2) + floor(c1 + 1) < 3 floor(c1 + 1)
; -3 < -3 x1 <= 0 ==> -2 < -3 x1 + 1 <= 1 ==> -2 <= floor(-3x1 + 1) <= 1
; ==> 0 <= floor(-3x1 + 1) + 2 <= 3
; hence, 0 < 2 floor(c1 + 1) \/ 1 < 2 floor(c1 + 1) \/ 2 < 2 floor(c1 + 1) \/ 3 < 2 floor(c1 + 1)

(assert
 (exists ((|x1| Real) )
    (<
     (+
      (to_int (+ (to_int (+ (* (+ 3 (- 6)) |x1|) 1))
		 2)
	      )
      (to_int (+ |c1| 1)))
     (* 3 (to_int (+ |c1| 1)))
     )
    ))
