; two Inv applications in one body: outside what cti.py handles
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x) (Inv y)) (Inv (+ x y)))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
