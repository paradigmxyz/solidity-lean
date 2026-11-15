def fastImpl (n : Nat) : Bool := n == n
@[implemented_by fastImpl] def slowEq (n : Nat) : Bool := true
theorem bad_impl : slowEq 3 = true := rfl
