(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

; test QE reduction for modulo
; 2x \equiv -3/2 mod 3 ==> 2x \equiv -2 mod 3 /\ floor(-3/2) = -2

(assert
 (exists ((|x1| Real) )
    (|mod| (* 2 |x1|) (- (/ 3 2)) 3)))
