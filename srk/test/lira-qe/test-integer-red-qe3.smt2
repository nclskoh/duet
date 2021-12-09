(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

; test QE reduction for nested floor and LEQ
; FORMULA: floor(floor( -3 x1 + 3/2 ) + (-3/2)) < c1 + 3/2
; -3x1 - 1 < c1 + 3/2 ==> -3x1 < c1 + 5/2 ==>
; -3x1 < floor(c1 + 5/2) \/ (-3x = floor(c1 + 5/2) /\ floor(c1 + 5/2) < c1 + 5/2

(assert
 (exists ((|x1| Real) )
    (<
     (to_int (+ (to_int (+ (* (+ 3 (- 6)) |x1|) (/ 3 2)))
		(- (/ 3 2))))
     (+ |c1| (/ 3 2)))
    ))
