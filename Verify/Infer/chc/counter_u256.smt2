; Counter.bump CHC, uint256 checked-arithmetic semantics
; vars: c0 = old(count), n, lim = limit, i, c = count
(set-logic HORN)
(declare-fun Inv (Int Int Int Int Int) Bool)
; init: entry state satisfies param ranges, contract invariant c0 <= lim, require(count + n <= limit) (checked add), i = 0, count = c0
(assert (forall ((c0 Int) (n Int) (lim Int))
  (=> (and (and (<= 0 c0) (< c0 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (and (<= 0 n) (< n 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (and (<= 0 lim) (< lim 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (<= c0 lim)
           (and (<= 0 (+ c0 n)) (< (+ c0 n) 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (<= (+ c0 n) lim))
      (Inv c0 n lim 0 c0))))
; step: body count++ (checked) then i++ (checked); a reverting op drops the path
(assert (forall ((c0 Int) (n Int) (lim Int) (i Int) (c Int))
  (=> (and (Inv c0 n lim i c) (< i n)
           (and (<= 0 (+ c 1)) (< (+ c 1) 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (and (<= 0 (+ i 1)) (< (+ i 1) 115792089237316195423570985008687907853269984665640564039457584007913129639936)))
      (Inv c0 n lim (+ i 1) (+ c 1)))))
; safety: on exit, ensures count == old(count) + n and contract invariant count <= limit
(assert (forall ((c0 Int) (n Int) (lim Int) (i Int) (c Int))
  (=> (and (Inv c0 n lim i c) (not (< i n))
           (not (and (= c (+ c0 n)) (<= c lim))))
      false)))
(check-sat)
(get-model)
