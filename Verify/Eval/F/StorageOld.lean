import Verify.Basic

/-!
# Lane F baseline: the storage fixtures by unfolding

Same statements as Storage.lean's fixtures, with `write` spelled out as the lambda `wp_sstore`
produces, proved the way Verify's proofs do today: `wp_sstore`, then `funext` and a case split on
which slot `k` is.
-/

namespace Verify.Eval.F.StorageFixtureOld

open SolidCore.Verify

def write (s : Storage) (slot v : Nat) : Storage :=
  fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k

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

theorem fixture16_old (herr : Revert → Prop) (s : Storage) :
    wp prog16 (fun _ _ s' => s' = write (write (write (write s 0 13) 1 14) 2 15) 3 16) herr s := by
  simp only [prog16, wp_bind, wp_sstore]
  funext k
  simp only [write]
  split_ifs <;> rfl

theorem fixture32_old (herr : Revert → Prop) (s : Storage) :
    wp prog32 (fun _ _ s' => s' = write (write (write (write s 0 29) 1 30) 2 31) 3 32) herr s := by
  simp only [prog32, wp_bind, wp_sstore]
  funext k
  simp only [write]
  split_ifs <;> rfl

theorem fixture64_old (herr : Revert → Prop) (s : Storage) :
    wp prog64 (fun _ _ s' => s' = write (write (write (write s 0 61) 1 62) 2 63) 3 64) herr s := by
  simp only [prog64, wp_bind, wp_sstore]
  funext k
  simp only [write]
  split_ifs <;> rfl

end Verify.Eval.F.StorageFixtureOld

#print axioms Verify.Eval.F.StorageFixtureOld.fixture64_old
