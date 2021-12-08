(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

(assert
 (exists ((|x1| Real) ) (<= (+ (+ (+
			     (* (* (/ 2 3) (- 3)) |x1|)
			     (* 2 |c1|))
			    (to_int (+ (to_int |x1|) (to_int |x1|))))
			 (* (+ 1 1) |x1|))
		      |x1|)))
