import Verify.Spec.Tree
import Verify.Spec.TreeSucceeds

/-!
# A returned word that is not a literal, from the erased tree

Regression checks for `tree_meets` and `tree_meets_fixed` on functions that return a word the
tree computes: `get` returns storage slot 0 (SimpleStorage's `get`, from Solidity by Example,
reduced to its one function), and `id` returns its argument unchanged. The erased tree spells
the word out as 32 `OByte.byteOf` bytes; `words_byteOf` reads them back as one word, `hsi` bounds
the storage word the spec loads, and `ham`, `hai` and `hml` bound the argument word. Without them
the bytes are evaluated one by one, `decodeWords` of the output never reduces, and `omega` fails. Each theorem's axioms are checked: no `sorryAx`.
-/

namespace SolidCore.Spec.TreeReturnCheck

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Generic

/-- `get() returns (uint256) { return num; }` and `id(uint256 x) returns (uint256) { return x; }`,
as solar-verify exports their specs. -/
def spec : Bundle where
  fuel := 0
  spec :=
  { name := "Return", fns := [], invariants := [], ghosts := [],
    specs := [
    { name := "Return.get", selector := 0x6d4ce63c, params := [], rets := [(.uint 256)],
      payable := false, requires := [],
      ensures := [(.bin .eq (.ret 0) (.load (.slot 0) (.lit 0) 32 (.uint 256)))],
      succeedsIf := [(.bin .eq (.env .value) (.lit 0))] },
    { name := "Return.id", selector := 0x7d3c40c8, params := [(.uint 256)], rets := [(.uint 256)],
      payable := false, requires := [],
      ensures := [(.bin .eq (.ret 0) (.arg 0))],
      succeedsIf := [] }] }

/-- The call context of the stage's calls. -/
def ctx : Ctx := { sender := 0x2000, value := 0, timestamp := 1, self := 0x1000 }

/-- The generic stage's erasure of `get`: return storage slot 0. -/
def getTree : Tree :=
  Tree.halt true
    [.byteOf (.init 0) 0, .byteOf (.init 0) 1, .byteOf (.init 0) 2, .byteOf (.init 0) 3,
     .byteOf (.init 0) 4, .byteOf (.init 0) 5, .byteOf (.init 0) 6, .byteOf (.init 0) 7,
     .byteOf (.init 0) 8, .byteOf (.init 0) 9, .byteOf (.init 0) 10, .byteOf (.init 0) 11,
     .byteOf (.init 0) 12, .byteOf (.init 0) 13, .byteOf (.init 0) 14, .byteOf (.init 0) 15,
     .byteOf (.init 0) 16, .byteOf (.init 0) 17, .byteOf (.init 0) 18, .byteOf (.init 0) 19,
     .byteOf (.init 0) 20, .byteOf (.init 0) 21, .byteOf (.init 0) 22, .byteOf (.init 0) 23,
     .byteOf (.init 0) 24, .byteOf (.init 0) 25, .byteOf (.init 0) 26, .byteOf (.init 0) 27,
     .byteOf (.init 0) 28, .byteOf (.init 0) 29, .byteOf (.init 0) 30, .byteOf (.init 0) 31]
    [] []


/-- The generic stage's erasure of `id`: return the argument. -/
def idTree : Tree :=
  Tree.halt true
    [.byteOf (.arg 0) 0, .byteOf (.arg 0) 1, .byteOf (.arg 0) 2, .byteOf (.arg 0) 3,
     .byteOf (.arg 0) 4, .byteOf (.arg 0) 5, .byteOf (.arg 0) 6, .byteOf (.arg 0) 7,
     .byteOf (.arg 0) 8, .byteOf (.arg 0) 9, .byteOf (.arg 0) 10, .byteOf (.arg 0) 11,
     .byteOf (.arg 0) 12, .byteOf (.arg 0) 13, .byteOf (.arg 0) 14, .byteOf (.arg 0) 15,
     .byteOf (.arg 0) 16, .byteOf (.arg 0) 17, .byteOf (.arg 0) 18, .byteOf (.arg 0) 19,
     .byteOf (.arg 0) 20, .byteOf (.arg 0) 21, .byteOf (.arg 0) 22, .byteOf (.arg 0) 23,
     .byteOf (.arg 0) 24, .byteOf (.arg 0) 25, .byteOf (.arg 0) 26, .byteOf (.arg 0) 27,
     .byteOf (.arg 0) 28, .byteOf (.arg 0) 29, .byteOf (.arg 0) 30, .byteOf (.arg 0) 31]
    [] []

def getSpec : FnSpec := spec.spec.specs[0]'(by decide)

def idSpec : FnSpec := spec.spec.specs[1]'(by decide)

set_option maxHeartbeats 4000000 in
/-- As `spec_connect.py` proves a spec without its succeeds-if conditions. -/
theorem get_meets0 : TreeMeetsFixed spec getSpec.noSucc ctx 0 getTree := by
  first
  | (tree_meets_map' [getTree, getSpec, SolidCore.Spec.FnSpec.noSucc, TreeReturnCheck.spec,
      TreeReturnCheck.ctx] SolidCore.Spec.mapSlotsSeparated_nil)
  | (tree_meets_fixed [getTree, getSpec, SolidCore.Spec.FnSpec.noSucc, TreeReturnCheck.spec,
      TreeReturnCheck.ctx])

set_option maxHeartbeats 4000000 in
theorem get_meets_any_ghost : TreeMeets spec getSpec.noSucc ctx 0 getTree := by
  tree_meets [getTree, getSpec, SolidCore.Spec.FnSpec.noSucc, TreeReturnCheck.spec, TreeReturnCheck.ctx]

set_option maxHeartbeats 4000000 in
theorem id_meets : TreeMeetsFixed spec idSpec ctx 1 idTree := by
  tree_meets_fixed [idTree, idSpec, TreeReturnCheck.spec, TreeReturnCheck.ctx]

set_option maxHeartbeats 4000000 in
theorem id_meets_any_ghost : TreeMeets spec idSpec ctx 1 idTree := by
  tree_meets [idTree, idSpec, TreeReturnCheck.spec, TreeReturnCheck.ctx]

/-- info: 'SolidCore.Spec.TreeReturnCheck.get_meets0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms get_meets0

/-- info: 'SolidCore.Spec.TreeReturnCheck.get_meets_any_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms get_meets_any_ghost

/-- info: 'SolidCore.Spec.TreeReturnCheck.id_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms id_meets

/-- info: 'SolidCore.Spec.TreeReturnCheck.id_meets_any_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms id_meets_any_ghost

end SolidCore.Spec.TreeReturnCheck
