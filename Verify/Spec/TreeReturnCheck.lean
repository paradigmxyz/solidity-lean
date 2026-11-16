import Verify.Spec.Tree
import Verify.Spec.TreeSucceeds

/-!
# A returned storage word, from the erased tree

Regression checks for `tree_meets` and `tree_meets_fixed` on a function that returns a word the
tree computes: `get` returns storage slot 0 (SimpleStorage's `get`, from Solidity by Example,
reduced to its one function). The erased tree spells the word out
as 32 `OByte.byteOf` bytes; `words_byteOf` reads them back as one word, and `hsi` bounds the
storage word the spec loads. Without them the bytes are evaluated one by one, `decodeWords` of the
output never reduces, and `omega` fails. Each theorem's axioms are checked: no `sorryAx`.
-/

namespace SolidCore.Spec.TreeReturnCheck

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Generic

/-- `get() returns (uint256) { return num; }`, as solar-verify exports its spec. -/
def spec : Bundle where
  fuel := 0
  spec :=
  { name := "Return", fns := [], invariants := [], ghosts := [],
    specs := [
    { name := "Return.get", selector := 0x6d4ce63c, params := [], rets := [(.uint 256)],
      payable := false, requires := [],
      ensures := [(.bin .eq (.ret 0) (.load (.slot 0) (.lit 0) 32 (.uint 256)))],
      succeedsIf := [(.bin .eq (.env .value) (.lit 0))] }] }

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


def getSpec : FnSpec := spec.spec.specs[0]'(by decide)

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

/-- info: 'SolidCore.Spec.TreeReturnCheck.get_meets0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms get_meets0

/-- info: 'SolidCore.Spec.TreeReturnCheck.get_meets_any_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms get_meets_any_ghost

end SolidCore.Spec.TreeReturnCheck
