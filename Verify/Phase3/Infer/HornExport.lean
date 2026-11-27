import Verify.LoopSource.Equiv.Emit

/-!
# Horn.ok_transfer: export the cut-point check's leaves (untrusted)

Evaluates `cut.check .off stage0 0xfd0011a5 1` and writes its leaves as JSON for
`tools/certify/loop_infer.py`. Nothing here is trusted: the obligation module recomputes the
leaves in the kernel (`leaves`).
-/

namespace Verify.Phase3.Infer.HornExport
open SolidCore.Refinement.Generic Verify.LoopSource.Equiv

/-- solar's lowered MIR for `Horn` (copied verbatim from `solar -Zemit-lean-stages`, `gen/Horn/Stage0.lean`). -/
def stage0 : SolarTV.MIR.Lowered.Module :=
  { entry := 2,
    functions := [
    -- @ok_transfer
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 29) .calldataload [.const 4]],
        .jump 1⟩,
      -- bb1
      ⟨[(5, [(0, .value 29), (3, .value 10)]), (6, [(0, .const 0), (3, .value 14)])],
        [.ne 8 (.value 5) (.const 0)],
        .branch (.value 8) 3 2⟩,
      -- bb2
      ⟨[],
        [.effect none .mstore [.const 0, .value 6]],
        .ret (.const 0) (.const 32)⟩,
      -- bb3
      ⟨[],
        [.pure 10 .sub [.value 5, .const 1],
         .pure 14 .add [.value 6, .const 1]],
        .jump 1⟩] },
    -- @bad_transfer
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 29) .calldataload [.const 4]],
        .jump 1⟩,
      -- bb1
      ⟨[(5, [(0, .value 29), (3, .value 10)]), (6, [(0, .const 0), (3, .value 14)])],
        [.ne 8 (.value 5) (.const 0)],
        .branch (.value 8) 3 2⟩,
      -- bb2
      ⟨[],
        [.effect none .mstore [.const 0, .value 6]],
        .ret (.const 0) (.const 32)⟩,
      -- bb3
      ⟨[],
        [.pure 10 .sub [.value 5, .const 1],
         .pure 14 .add [.value 6, .const 1]],
        .jump 1⟩] },
    -- @entry
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 0) .callvalue [],
         .effect (some 1) .calldatasize [],
         .pure 3 .lt [.value 1, .const 36],
         .word 4 (.value 3),
         .pure 5 .or [.value 0, .value 4],
         .ne 7 (.value 5) (.const 0)],
        .branch (.value 7) 1 2⟩,
      -- bb1
      ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩,
      -- bb2
      ⟨[],
        [.effect (some 9) .calldataload [.const 0],
         .pure 11 .shr [.const 224, .value 9]],
        .switch (.value 11) 1 [(.const 0x18a4b471, 3), (.const 0xfd0011a5, 4)]⟩,
      -- bb3
      ⟨[],
        [],
        .tailCall 1 []⟩,
      -- bb4
      ⟨[],
        [],
        .tailCall 0 []⟩] }] }


/-- The cut-point certificate of `ok_transfer`'s loop (copied from `loop_equiv.py`'s `Cut.lean`; untrusted, checked by `Cut.check`). -/
def cut : Cut :=
  { fn := 0, head := 1,
    ids := [
      (0, (.fixed (.lit 0))),
      (1, (.fixed (.lit 0))),
      (3, (.fixed (.lit 0))),
      (4, (.fixed (.lit 0))),
      (5, (.hw 0)),
      (6, (.hw 1)),
      (7, (.fixed (.lit 0))),
      (8, (.hw 2)),
      (9, (.fixed (.lit 0))),
      (10, (.hw 3)),
      (11, (.fixed (.lit 0))),
      (14, (.hw 4)),
      (29, (.fixed (.arg 0)))],
    mem := [], writes := [], nhw := 5,
    cases := [[]],
    fuel := 60 }


def q (s : String) : String := "\"" ++ s ++ "\""

def binS : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .lt => "lt" | .gt => "gt"
  | .eq => "eq" | .and => "and" | .or => "or" | .xor => "xor" | .shl => "shl" | .shr => "shr"
  | .byte => "byte"

def unS : UnOp → String
  | .iszero => "iszero" | .not => "not"

def wj : WExpr → String
  | .lit n => s!"[\"lit\",{n}]"
  | .arg i => s!"[\"arg\",{i}]"
  | .init k => s!"[\"init\",{k}]"
  | .un op a => s!"[\"un\",{q (unS op)},{wj a}]"
  | .bin op a b => s!"[\"bin\",{q (binS op)},{wj a},{wj b}]"
  | .sinit k => s!"[\"sinit\",{wj k}]"
  | .sel c a b => s!"[\"sel\",{wj c},{wj a},{wj b}]"
  | .hash a b => s!"[\"hash\",{wj a},{wj b}]"
  | .caller => "[\"caller\"]"

def arr (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def bj : OByte → String
  | .lit b => s!"[\"blit\",{b}]"
  | .byteOf e i => s!"[\"byteOf\",{wj e},{i}]"

def tj : Tree → String
  | .halt ok out ws ls =>
    s!"[\"halt\",{ok},{arr (out.map bj)},{arr (ws.map fun w => arr [wj w.1, wj w.2])},{ls.length}]"
  | .ite c t e => s!"[\"ite\",{wj c},{tj t},{tj e}]"

def kj (K : Facts) : String := arr (K.map fun p => arr [wj p.1, toString p.2])

def oj : Out → String
  | .exit T => s!"[\"exit\",{tj T}]"
  | .back hs => s!"[\"back\",{arr (hs.map wj)}]"

def lj (ls : List (Facts × Out)) : String := arr (ls.map fun p => arr [kj p.1, oj p.2])

def json : String :=
  match cut.check .off stage0 0xfd0011a5 1 with
  | some (le, li) =>
    s!"\{\"format\":\"loop leaves 1\",\"fn\":\"ok_transfer\",\"sel\":{0xfd0011a5},\"n\":1,\"nhw\":{cut.nhw},\"cases\":{arr (cut.cases.map kj)},\"le\":{lj le},\"li\":{lj li}}"
  | none => "null"

#eval IO.FS.writeFile "/home/hand/simp/p3/horn/leaves.json" (json ++ "\n")
#eval IO.FS.writeFile "/home/hand/simp/p3/horn/leaves.repr" (reprStr (cut.check .off stage0 0xfd0011a5 1) ++ "\n")
#eval (cut.check .off stage0 0xfd0011a5 1).map fun r => (r.1.length, r.2.length)

end Verify.Phase3.Infer.HornExport
