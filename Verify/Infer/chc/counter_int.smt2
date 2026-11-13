; Counter.bump CHC, mathematical Int (uint params >= 0, no overflow guards) semantics
; vars: c0 = old(count), n, lim = limit, i, c = count
(set-logic HORN)
(declare-fun Inv (Int Int Int Int Int) Bool)
; init: entry state satisfies param ranges, contract invariant c0 <= lim, require(count + n <= limit) (checked add), i = 0, count = c0
(assert (forall ((c0 Int) (n Int) (lim Int))
  (=> (and (<= 0 c0) (<= 0 n) (<= 0 lim) (<= c0 lim)
            (<= (+ c0 n) lim))
      (Inv c0 n lim 0 c0))))
; step: body count++ (checked) then i++ (checked); a reverting op drops the path
(assert (forall ((c0 Int) (n Int) (lim Int) (i Int) (c Int))
  (=> (and (Inv c0 n lim i c) (< i n)
           )
      (Inv c0 n lim (+ i 1) (+ c 1)))))
; safety: on exit, ensures count == old(count) + n and contract invariant count <= limit
(assert (forall ((c0 Int) (n Int) (lim Int) (i Int) (c Int))
  (=> (and (Inv c0 n lim i c) (not (< i n))
           (not (and (= c (+ c0 n)) (<= c lim))))
      false)))
(check-sat)
(get-model)
