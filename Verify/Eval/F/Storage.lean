import Verify.Basic

/-!
# Lane F: storage writes as function updates

`SolidCore.Verify.sstore` (Verify/Basic.lean:87) leaves
`fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k`, and `wp_sstore`
(Verify/Basic.lean:97) puts that lambda into every goal. Here the lambda gets a name, `write`
(`rfl` to it), and the laws of a function update: read after write at the same slot and at
another slot, write after write at the same slot, and commuting writes to distinct slots, with a
sorted form `simp` can use as a rewrite system on concrete slots. Slots are compared modulo
2^256, as `sstore` does. Core and the module under test only.
-/

namespace Verify.Eval.F

open SolidCore.Verify

set_option linter.deprecated false

/-- What `sstore slot v` leaves, named. Definitionally the lambda in `wp_sstore`. -/
def write (s : Storage) (slot v : Nat) : Storage :=
  fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k

theorem sstore_eq_write (slot v : Nat) : sstore slot v = fun s => .ok ((), write s slot v) := rfl

/-- `wp_sstore` in the named form. Use it with `-wp_sstore` (or in `simp only`). -/
theorem wp_sstore_write (slot v : Nat) (post : Unit → Assn) :
    wp (sstore slot v) post = fun herr s => post () herr (write s slot v) :=
  wp_sstore slot v post

/-- Fold the lambda `wp_sstore` produces back into `write`. -/
theorem lam_eq_write (s : Storage) (slot v : Nat) :
    (fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k) = write s slot v := rfl

/-! ## Reads -/

@[simp, grind =] theorem write_apply_self (s : Storage) (slot v : Nat) :
    write s slot v slot = v % 2 ^ 256 := by simp [write]

theorem write_apply_same {s : Storage} {slot k : Nat} (v : Nat) (h : k % 2 ^ 256 = slot % 2 ^ 256) :
    write s slot v k = v % 2 ^ 256 := by
  show (if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k) = _; rw [if_pos h]

@[simp] theorem write_apply_other {s : Storage} {slot k : Nat} (v : Nat)
    (h : k % 2 ^ 256 ≠ slot % 2 ^ 256) : write s slot v k = s k := by
  show (if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k) = _; rw [if_neg h]

@[grind =] theorem write_apply (s : Storage) (slot v k : Nat) :
    write s slot v k = if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k := rfl

/-! ## Writes -/

theorem write_write_same {s : Storage} {a b : Nat} (v u : Nat) (h : a % 2 ^ 256 = b % 2 ^ 256) :
    write (write s a v) b u = write s b u := by
  funext k; simp only [write]; split <;> simp_all

@[simp] theorem write_write_self (s : Storage) (a v u : Nat) :
    write (write s a v) a u = write s a u := write_write_same v u rfl

theorem write_comm {s : Storage} {a b : Nat} (v u : Nat) (h : a % 2 ^ 256 ≠ b % 2 ^ 256) :
    write (write s a v) b u = write (write s b u) a v := by
  funext k; simp only [write]; split <;> split <;> simp_all

/-- The sorted form for `simp`: an outer write to a smaller slot moves inward. Terminates on
concrete slots, where the side condition is decided. -/
@[simp] theorem write_comm_lt {s : Storage} {a b : Nat} (v u : Nat)
    (h : b % 2 ^ 256 < a % 2 ^ 256) :
    write (write s a v) b u = write (write s b u) a v :=
  write_comm v u (by omega)

/-- An outer write to the same slot as one below another write absorbs it (with sorted writes,
the same slot meets itself after one commute). -/
theorem write_write_write_same {s : Storage} {a b : Nat} (v w u : Nat)
    (h : a % 2 ^ 256 ≠ b % 2 ^ 256) :
    write (write (write s a v) b w) a u = write (write s b w) a u := by
  rw [write_comm w u (Ne.symm h), write_write_self, write_comm u w h]

end Verify.Eval.F

/-! ## Fixtures: N writes cycling over slots 0..3 leave four writes (new). Old: StorageOld.lean -/

namespace Verify.Eval.F.StorageFixture

open SolidCore.Verify Verify.Eval.F

def prog16 : SolM Unit := do
  sstore 0 1
  sstore 1 2
  sstore 2 3
  sstore 3 4
  sstore 0 5
  sstore 1 6
  sstore 2 7
  sstore 3 8
  sstore 0 9
  sstore 1 10
  sstore 2 11
  sstore 3 12
  sstore 0 13
  sstore 1 14
  sstore 2 15
  sstore 3 16

def prog32 : SolM Unit := do
  sstore 0 1
  sstore 1 2
  sstore 2 3
  sstore 3 4
  sstore 0 5
  sstore 1 6
  sstore 2 7
  sstore 3 8
  sstore 0 9
  sstore 1 10
  sstore 2 11
  sstore 3 12
  sstore 0 13
  sstore 1 14
  sstore 2 15
  sstore 3 16
  sstore 0 17
  sstore 1 18
  sstore 2 19
  sstore 3 20
  sstore 0 21
  sstore 1 22
  sstore 2 23
  sstore 3 24
  sstore 0 25
  sstore 1 26
  sstore 2 27
  sstore 3 28
  sstore 0 29
  sstore 1 30
  sstore 2 31
  sstore 3 32

def prog64 : SolM Unit := do
  sstore 0 1
  sstore 1 2
  sstore 2 3
  sstore 3 4
  sstore 0 5
  sstore 1 6
  sstore 2 7
  sstore 3 8
  sstore 0 9
  sstore 1 10
  sstore 2 11
  sstore 3 12
  sstore 0 13
  sstore 1 14
  sstore 2 15
  sstore 3 16
  sstore 0 17
  sstore 1 18
  sstore 2 19
  sstore 3 20
  sstore 0 21
  sstore 1 22
  sstore 2 23
  sstore 3 24
  sstore 0 25
  sstore 1 26
  sstore 2 27
  sstore 3 28
  sstore 0 29
  sstore 1 30
  sstore 2 31
  sstore 3 32
  sstore 0 33
  sstore 1 34
  sstore 2 35
  sstore 3 36
  sstore 0 37
  sstore 1 38
  sstore 2 39
  sstore 3 40
  sstore 0 41
  sstore 1 42
  sstore 2 43
  sstore 3 44
  sstore 0 45
  sstore 1 46
  sstore 2 47
  sstore 3 48
  sstore 0 49
  sstore 1 50
  sstore 2 51
  sstore 3 52
  sstore 0 53
  sstore 1 54
  sstore 2 55
  sstore 3 56
  sstore 0 57
  sstore 1 58
  sstore 2 59
  sstore 3 60
  sstore 0 61
  sstore 1 62
  sstore 2 63
  sstore 3 64

theorem fixture16 (herr : Revert → Prop) (s : Storage) :
    wp prog16 (fun _ _ s' => s' = write (write (write (write s 0 13) 1 14) 2 15) 3 16) herr s := by
  simp only [prog16, wp_bind, wp_sstore_write]
  simp

theorem fixture32 (herr : Revert → Prop) (s : Storage) :
    wp prog32 (fun _ _ s' => s' = write (write (write (write s 0 29) 1 30) 2 31) 3 32) herr s := by
  simp only [prog32, wp_bind, wp_sstore_write]
  simp

theorem fixture64 (herr : Revert → Prop) (s : Storage) :
    wp prog64 (fun _ _ s' => s' = write (write (write (write s 0 61) 1 62) 2 63) 3 64) herr s := by
  simp only [prog64, wp_bind, wp_sstore_write]
  simp

end Verify.Eval.F.StorageFixture

/-- info: 'Verify.Eval.F.write_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Verify.Eval.F.write_comm
#print axioms Verify.Eval.F.write_write_same
#print axioms Verify.Eval.F.write_comm_lt
#print axioms Verify.Eval.F.StorageFixture.fixture64
