(set-info :smt-lib-version 2.6)
(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun |mod| (Real Real Real) (Bool))
(declare-const |c1| (Real))

(assert
 (exists ((|x1| Real) ) (|mod| |x1| 2 3)))
