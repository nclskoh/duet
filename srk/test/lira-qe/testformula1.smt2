(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |testf| (Real) (Real))
(declare-fun |mod| (Real Real Real) (Bool))

(declare-const |i1| (Real))
(declare-const |i2| (Real))
; (assert (= (testf |i1|) |i1|))
(assert (= (to_int |i2|) |i2|))

(assert
 (forall ((|x1| Real) )
	 (exists ((|x3| Real) )
	    (let ((?x1_int (= (to_int |x1|) |x1|))
		  (?r13 (not (> (* (/ 2 1) |x1|) |x3|)))
		  (?r32 (<= |x3| (* (+ 1.1 0.9) |i2|)))
		  (?r3 (|mod| |x3| 1 2)))
	      (and ?x1_int
		   (and ?r13
			(and ?r32 ?r3)))))))
