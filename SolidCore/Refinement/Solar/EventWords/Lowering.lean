import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.KernelCopies
import SolidCore.Refinement.KernelRfl
import SolidCore.Refinement.Source.EventWords
import event_words.gen.EventWords.Stage0

/-!
# event_words: the generic source stage on solar's own module

scripts/refinement/mem/event_words.sol,

    contract EventWords {
      event Swap(address indexed sender, uint256 amount0In, uint256 amount1In,
                 uint256 amount0Out, uint256 amount1Out, address indexed to);
      function swap(uint256 a0, uint256 a1, uint256 b0, uint256 b1, address to) external {
        emit Swap(msg.sender, a0, a1, b0, b1, to); } }

logs with three topics (the signature's, the caller, `to`) and four data words, the shape of
Uniswap v2's `Swap`, `Mint`, `Burn` and `Sync` events. Solar ABI-encodes the data at the free
memory pointer: its first lowered MIR module stores the entry heap `0x80` at `0x40` on entering
`swap` (`Function.entryHeap`), reads it back with `mload 0x40` against the `heap_floor`, and
writes the four words from there before `log 3`. The generic symbolic run takes the entry heap,
the heap floor and the constant `mload` (`Generic.symStart`, `symInsts`, `symEffect`).

* `shape_eq`: `EventWords` type checks, its core is `coreLit`, its constructor leaves no storage;
* `check_stage0`, `checkValue_stage0`: the generic check with the caller-only flags accepts
  stage0 for `swap` (`decide +kernel`), at no value and at any value;
* `check_rejects_caller`, `check_rejects_topic`, `check_rejects_order`, `check_rejects_data`,
  `check_rejects_heap`: it rejects stage0 with the caller topic replaced by an argument, with the
  signature topic changed, with the two indexed topics swapped, with two data words swapped and
  with another entry heap;
* `lowering`, `loweringValue`: the stage from SolidCore to stage0 on every call of `swap`, from
  any storage, under every oracle with SolidCore's caller (`Generic.CallerOk`).

No sorry, native_decide or bv_decide.
-/

namespace SolidCore.Refinement.Solar.EventWords

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- The interpreter fuel of the symbolic run of the module: steps along each path. -/
def mirFuel : Nat := 40

/-- SolidCore's checked `EventWords`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.EventWords.importedSourceUnit "EventWords"

/-- The selector of `swap(uint256,uint256,uint256,uint256,address)`. -/
abbrev swapSel : Nat := 0x562e19df

/-- `swap` and its parameters. -/
def fnSwap : Fn := ⟨swapSel, [.uint 256, .uint 256, .uint 256, .uint 256, .uint 160]⟩

/-- The external function of `EventWords`. -/
def fns : List Fn := [fnSwap]

/-- SolidCore's core contract of `EventWords`, as the type checker leaves it. -/
def coreLit : Contract :=
  { storageFields := [],
    immutableFields := [],
    eventDecls := [{ name := "Swap",
                     indexedCount := 2,
                     topic? := some 97492587597809768260878645486617631645481691101407825574583615073533464008738,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false },
                                { ty := SolidCore.Solidity.Source.Ty.address, indexed := true }] },
                   { name := "EventWords.Swap",
                     indexedCount := 2,
                     topic? := some 97492587597809768260878645486617631645481691101407825574583615073533464008738,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false },
                                { ty := SolidCore.Solidity.Source.Ty.address, indexed := true }] }],
    errorDecls := [],
    functions := [{ name := "swap",
                    selector? := some 1445861855,
                    payable := false,
                    params := [{ name := "a0",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "a1",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "b0",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "b1",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "to",
                                 ty := SolidCore.Solidity.Source.Ty.address,
                                 isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a0")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "a0")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a1")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "a1")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b0")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "b0")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b1")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "b1")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Swap"
                                    [SolidCore.Solidity.Source.Expr.caller,
                                     SolidCore.Solidity.Source.Expr.var "a0",
                                     SolidCore.Solidity.Source.Expr.var "a1",
                                     SolidCore.Solidity.Source.Expr.var "b0",
                                     SolidCore.Solidity.Source.Expr.var "b1",
                                     SolidCore.Solidity.Source.Expr.var "to"]]],
                    dispatchId? := none },
                  { name := "__internal_swap(uint256,uint256,uint256,uint256,address)#[SolidCore.Solidity.Ty.uint 256, SolidCore.Solidity.Ty.uint 256, SolidCore.Solidity.Ty.uint 256, SolidCore.Solidity.Ty.uint 256, SolidCore.Solidity.Ty.address false]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "a0",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "a1",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "b0",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "b1",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "to",
                                 ty := SolidCore.Solidity.Source.Ty.address,
                                 isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a0")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "a0")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a1")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "a1")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b0")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "b0")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b1")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "b1")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Swap"
                                    [SolidCore.Solidity.Source.Expr.caller,
                                     SolidCore.Solidity.Source.Expr.var "a0",
                                     SolidCore.Solidity.Source.Expr.var "a1",
                                     SolidCore.Solidity.Source.Expr.var "b0",
                                     SolidCore.Solidity.Source.Expr.var "b1",
                                     SolidCore.Solidity.Source.Expr.var "to"]]],
                    dispatchId? := none }] }

/-! ## The selectors and the event's signature topic

The type checker computes each external function's selector and the event's topic by
Keccak-256, which costs the kernel about 400 MB a hash: each is checked once, alone, and the
check of the shape below runs on copies that read them from tables. -/
/-- The selector of `swap(uint256,uint256,uint256,uint256,address)`, by Keccak-256 of its signature. -/
def selSwap : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "swap(uint256,uint256,uint256,uint256,address)"

kernel_rfl selSwap_eq selSwap swapSel
/-- The topic of `Swap(address,uint256,uint256,uint256,uint256,address)`, by Keccak-256 of its signature. -/
def topic : Nat := SolidCore.Solidity.Source.Keccak.digestWord "Swap(address,uint256,uint256,uint256,uint256,address)"

kernel_rfl topic_eq topic 0xd78ad95fa46c994b6551d0da85fc275fe613ce37657fb8d5e3d130840159d822

/-- `ABI.selectorFromSignature`, with `EventWords`'s signatures by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "swap(uint256,uint256,uint256,uint256,address)" then swapSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split
  · next h => subst h; exact selSwap_eq
  · rfl

/-- `Keccak.digestWord`, with the event's signature by table. -/
def digestTable (s : String) : Nat :=
  if s = "Swap(address,uint256,uint256,uint256,uint256,address)" then 0xd78ad95fa46c994b6551d0da85fc275fe613ce37657fb8d5e3d130840159d822 else SolidCore.Solidity.Source.Keccak.digestWord s

theorem digest_eq : SolidCore.Solidity.Source.Keccak.digestWord = digestTable := by
  funext s
  unfold digestTable
  split
  · next h => subst h; exact topic_eq
  · rfl

/-- SolidCore's checked core of `EventWords`, and whether its constructor leaves no storage and no
logs, when `EventWords` type checks. -/
def shape? : Option (Contract × Bool) :=
  match contract? with
  | .ok c => some (c.core, Wide.deployedAt fuel c [])
  | .error _ => none

-- `shape_eq : shape? = some (coreLit, true)`: `EventWords` type checks, its core is `coreLit` and its
-- constructor leaves no storage, by the kernel's conversion check on the copy of `shape?` that
-- reads the selectors and the topic from their tables.
kernel_rfl shape_eq shape? (some (coreLit, true)) using selector_eq digest_eq

/-! ## The check on solar's module -/
set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `swap`. -/
theorem check_swap :
    Generic.check fuel mirFuel coreLit SolarTV.Export.EventWords.stage0 [fnSwap] .callerOnly = true := by
  decide +kernel

/-- The generic check accepts stage0 for every external function. -/
theorem check_stage0 :
    Generic.check fuel mirFuel coreLit SolarTV.Export.EventWords.stage0 fns .callerOnly = true := by
  have h0 := check_swap
  simp only [Generic.check, List.all_cons, List.all_nil, Bool.and_true] at h0
  simp only [Generic.check, fns, List.all_cons, List.all_nil, Bool.and_true, h0]

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: no function is payable, and stage0 reverts with empty output on a
call of each with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue mirFuel coreLit SolarTV.Export.EventWords.stage0 fns .callerOnly = true := by
  decide +kernel

/-! ## Mutants the check rejects -/

/-- stage0 with each instruction of function `i` changed by `f`. -/
def mapFn (i : Nat) (f : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst) :
    SolarTV.MIR.Lowered.Module :=
  { SolarTV.Export.EventWords.stage0 with
    functions := SolarTV.Export.EventWords.stage0.functions.mapIdx fun j fn =>
      if j = i then { fn with blocks := fn.blocks.map fun b => { b with insts := b.insts.map f } }
      else fn }
/-- `swap` logging an argument word as the caller topic. -/
def noCaller : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect (some 6) .caller [] => .effect (some 6) .calldataload [.const 4]
  | i => i

/-- `swap`'s log with another signature topic. -/
def wrongTopic : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none (.log 3) [a, b, .const t, c, d] => .effect none (.log 3) [a, b, .const (t + 1), c, d]
  | i => i

/-- `swap`'s log with its indexed topics swapped. -/
def swapTopics : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none (.log 3) [a, b, t, c, d] => .effect none (.log 3) [a, b, t, d, c]
  | i => i

/-- `swap` writing its first two data words in each other's place. -/
def swapData : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none .mstore [.value 45, .value 17] => .effect none .mstore [.value 45, .value 19]
  | .effect none .mstore [.value 33, .value 19] => .effect none .mstore [.value 33, .value 17]
  | i => i

/-- stage0 with `swap`'s entry heap moved by a word, so that its `assume` on the free memory
pointer fails. -/
def wrongHeap : SolarTV.MIR.Lowered.Module :=
  { SolarTV.Export.EventWords.stage0 with
    functions := SolarTV.Export.EventWords.stage0.functions.mapIdx fun j fn =>
      if j = 0 then { fn with entryHeap := some 160 } else fn }

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `swap` logging an argument as the caller. -/
theorem check_rejects_caller :
    Generic.check fuel mirFuel coreLit (mapFn 0 noCaller) fns .callerOnly = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `swap` with the wrong signature topic. -/
theorem check_rejects_topic :
    Generic.check fuel mirFuel coreLit (mapFn 0 wrongTopic) fns .callerOnly = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `swap` with its topics swapped. -/
theorem check_rejects_order :
    Generic.check fuel mirFuel coreLit (mapFn 0 swapTopics) fns .callerOnly = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `swap` with two data words swapped. -/
theorem check_rejects_data :
    Generic.check fuel mirFuel coreLit (mapFn 0 swapData) fns .callerOnly = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects stage0 with another entry heap. -/
theorem check_rejects_heap :
    Generic.check fuel mirFuel coreLit wrongHeap fns .callerOnly = false := by
  decide +kernel

/-! ## The stage -/

/-- The checked contract has the core `coreLit`, and its constructor leaves no storage. -/
theorem deployed_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core = coreLit ∧ ∃ d, Wide.DeployedAt fuel c d [] := by
  have h := shape_eq
  unfold shape? at h
  rw [hc] at h
  obtain ⟨hk, hd⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hk, Wide.deployedAt_of hd⟩

/-- **The source stage of `EventWords`**: every call of `swap` on any argument words, no value,
from any storage, under every oracle whose caller is SolidCore's (`Generic.CallerOk`): `EventWords`
hashes nothing at run time, so the check runs with the caller-only flags. -/
theorem lowering (o : SolarTV.Machine.Oracle) (henv : Generic.CallerOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.EventWords.stage0 (fun call => ∃ σ, fullScope fns σ call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageCaller o henv hd (by rw [hk]; exact check_stage0)

/-- **The source stage of `EventWords` at every value**: the same calls with any value below `2 ^ 256`: `swap` is not payable, and both sides revert with empty data. -/
theorem loweringValue (o : SolarTV.Machine.Oracle) (henv : Generic.CallerOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.EventWords.stage0 (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageValueCaller o henv hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

#print axioms selector_eq

#print axioms digest_eq

#print axioms shape_eq

#print axioms check_stage0

#print axioms checkValue_stage0

#print axioms check_rejects_caller

#print axioms check_rejects_topic

#print axioms check_rejects_order

#print axioms check_rejects_data

#print axioms check_rejects_heap

#print axioms lowering

#print axioms loweringValue

end SolidCore.Refinement.Solar.EventWords
