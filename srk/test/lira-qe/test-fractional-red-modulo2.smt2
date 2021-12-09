(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

; test QE reduction for modulo
; 2x \equiv 5/2 mod 3 ==> 2x = 1/2 + {0, 1} /\ 2 \equiv {0, 1} mod 3.

(assert
 (exists ((|x1| Real) )
    (|mod| (* 2 |x1|) (/ 5 2) 3)))
