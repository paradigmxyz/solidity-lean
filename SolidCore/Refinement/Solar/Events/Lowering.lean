import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.KernelCopies
import SolidCore.Refinement.KernelRfl
import SolidCore.Refinement.Source.Events
import events.gen.Events.Stage0

/-!
# events: the generic source stage on solar's own module

solar-tv/milestone/events/events.sol (sha256
8b951679cab695d07c193e56dd5d96d14a1c63976673c79a72c690f07c50b5b0, copied to
scripts/refinement/events/events.sol),

    contract Events {
      event Transfer(address indexed from, uint256 indexed id, uint256 value);
      function transfer(uint256 id, uint256 value) external { emit Transfer(msg.sender, id, value); } }

logs with three topics (the signature's, the caller, `id`) and `value`'s word as data.
`SolarTV.Export.Events.stage0` is solar's first lowered MIR module for it (solar 0a455fda),
from solar's solar-tv/milestone/events, whose backend stages solar's milestone proves
(`SolarTV.Milestone.Events.events_mir_to_evmir`): `log 3` of the memory word 0 with the
signature, `caller` and the first argument as topics.

* `shape_eq`: `Events` type checks, its core is `coreLit`, its constructor leaves no storage;
* `check_stage0`, `checkValue_stage0`: the generic check with the caller-only flags accepts
  stage0 for `transfer` (`decide +kernel`), at no value and at any value;
* `check_rejects_caller`, `check_rejects_topic`, `check_rejects_order`: it rejects stage0
  with the caller topic replaced by the value, with the signature topic changed, and with the
  two indexed topics swapped;
* `lowering`, `loweringValue`: the stage from SolidCore to stage0 on every call of
  `transfer`, from any storage, under every oracle with SolidCore's caller (`Generic.CallerOk`).

No sorry, native_decide or bv_decide.
-/

namespace SolidCore.Refinement.Solar.Events

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- The interpreter fuel of the symbolic run of the module: steps along each path. -/
def mirFuel : Nat := 40

/-- SolidCore's checked `Events`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.Events.importedSourceUnit "Events"

/-- The selector of `transfer(uint256,uint256)`. -/
abbrev transferSel : Nat := 0x0cf79e0a

/-- `transfer` and its parameters. -/
def fnTransfer : Fn := ⟨transferSel, [.uint 256, .uint 256]⟩

/-- The external function of `Events`. -/
def fns : List Fn := [fnTransfer]

/-- SolidCore's core contract of `Events`, as the type checker leaves it. -/
def coreLit : Contract :=
  { storageFields := [],
    immutableFields := [],
    eventDecls := [{ name := "Transfer",
                     indexedCount := 2,
                     topic? := some 57743509088182381206199446994789903859235539828100749539486038820882091805673,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false }] },
                   { name := "Events.Transfer",
                     indexedCount := 2,
                     topic? := some 57743509088182381206199446994789903859235539828100749539486038820882091805673,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false }] }],
    errorDecls := [],
    functions := [{ name := "transfer",
                    selector? := some 217554442,
                    payable := false,
                    params := [{ name := "id", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false },
                               { name := "value", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "id")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "id")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "value")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "value")),
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Transfer"
                                    [SolidCore.Solidity.Source.Expr.caller,
                                     SolidCore.Solidity.Source.Expr.var "id",
                                     SolidCore.Solidity.Source.Expr.var "value"]]],
                    dispatchId? := none },
                  { name := "__internal_transfer(uint256,uint256)#[SolidCore.Solidity.Ty.uint 256, SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "id", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false },
                               { name := "value", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "id")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "id")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "value")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "value")),
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Transfer"
                                    [SolidCore.Solidity.Source.Expr.caller,
                                     SolidCore.Solidity.Source.Expr.var "id",
                                     SolidCore.Solidity.Source.Expr.var "value"]]],
                    dispatchId? := none }] }

/-! ## The selectors and the event's signature topic

The type checker computes each external function's selector and the event's topic by
Keccak-256, which costs the kernel about 400 MB a hash: each is checked once, alone, and the
check of the shape below runs on copies that read them from tables. -/
/-- The selector of `transfer(uint256,uint256)`, by Keccak-256 of its signature. -/
def selTransfer : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "transfer(uint256,uint256)"

kernel_rfl selTransfer_eq selTransfer transferSel
/-- The topic of `Transfer(address,uint256,uint256)`, by Keccak-256 of its signature. -/
def topic : Nat := SolidCore.Solidity.Source.Keccak.digestWord "Transfer(address,uint256,uint256)"

kernel_rfl topic_eq topic 0x7fa9aafeb8bb803d77de5d84bc2f2edbd842ca91b20cd5020aa21dfe26ab0be9

/-- `ABI.selectorFromSignature`, with `Events`'s signatures by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "transfer(uint256,uint256)" then transferSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split
  · next h => subst h; exact selTransfer_eq
  · rfl

/-- `Keccak.digestWord`, with the event's signature by table. -/
def digestTable (s : String) : Nat :=
  if s = "Transfer(address,uint256,uint256)" then 0x7fa9aafeb8bb803d77de5d84bc2f2edbd842ca91b20cd5020aa21dfe26ab0be9 else SolidCore.Solidity.Source.Keccak.digestWord s

theorem digest_eq : SolidCore.Solidity.Source.Keccak.digestWord = digestTable := by
  funext s
  unfold digestTable
  split
  · next h => subst h; exact topic_eq
  · rfl

/-- SolidCore's checked core of `Events`, and whether its constructor leaves no storage and no
logs, when `Events` type checks. -/
def shape? : Option (Contract × Bool) :=
  match contract? with
  | .ok c => some (c.core, Wide.deployedAt fuel c [])
  | .error _ => none

-- `shape_eq : shape? = some (coreLit, true)`: `Events` type checks, its core is `coreLit` and its
-- constructor leaves no storage, by the kernel's conversion check on the copy of `shape?` that
-- reads the selectors and the topic from their tables.
kernel_rfl shape_eq shape? (some (coreLit, true)) using selector_eq digest_eq

/-! ## The check on solar's module -/
set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `transfer`. -/
theorem check_transfer :
    Generic.check fuel mirFuel coreLit SolarTV.Export.Events.stage0 [fnTransfer] .callerOnly = true := by
  decide +kernel

/-- The generic check accepts stage0 for every external function. -/
theorem check_stage0 :
    Generic.check fuel mirFuel coreLit SolarTV.Export.Events.stage0 fns .callerOnly = true := by
  have h0 := check_transfer
  simp only [Generic.check, List.all_cons, List.all_nil, Bool.and_true] at h0
  simp only [Generic.check, fns, List.all_cons, List.all_nil, Bool.and_true, h0]

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: no function is payable, and stage0 reverts with empty output on a
call of each with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue mirFuel coreLit SolarTV.Export.Events.stage0 fns .callerOnly = true := by
  decide +kernel

/-! ## Mutants the check rejects -/

/-- stage0 with each instruction of function `i` changed by `f`. -/
def mapFn (i : Nat) (f : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst) :
    SolarTV.MIR.Lowered.Module :=
  { SolarTV.Export.Events.stage0 with
    functions := SolarTV.Export.Events.stage0.functions.mapIdx fun j fn =>
      if j = i then { fn with blocks := fn.blocks.map fun b => { b with insts := b.insts.map f } }
      else fn }
/-- `transfer` logging its value word as the caller topic. -/
def noCaller : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect (some 3) .caller [] => .effect (some 3) .calldataload [.const 36]
  | i => i

/-- `transfer`'s log with another signature topic. -/
def wrongTopic : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none (.log 3) [a, b, .const t, c, d] => .effect none (.log 3) [a, b, .const (t + 1), c, d]
  | i => i

/-- `transfer`'s log with its indexed topics swapped. -/
def swapTopics : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none (.log 3) [a, b, t, c, d] => .effect none (.log 3) [a, b, t, d, c]
  | i => i

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `transfer` logging the value as the caller. -/
theorem check_rejects_caller :
    Generic.check fuel mirFuel coreLit (mapFn 0 noCaller) fns .callerOnly = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `transfer` with the wrong signature topic. -/
theorem check_rejects_topic :
    Generic.check fuel mirFuel coreLit (mapFn 0 wrongTopic) fns .callerOnly = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `transfer` with its topics swapped. -/
theorem check_rejects_order :
    Generic.check fuel mirFuel coreLit (mapFn 0 swapTopics) fns .callerOnly = false := by
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

/-- **The source stage of `Events`**: every call of `transfer` on any argument words, no value,
from any storage, under every oracle whose caller is SolidCore's (`Generic.CallerOk`): `Events`
hashes nothing at run time, so the check runs with the caller-only flags. -/
theorem lowering (o : SolarTV.Machine.Oracle) (henv : Generic.CallerOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Events.stage0 (fun call => ∃ σ, fullScope fns σ call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageCaller o henv hd (by rw [hk]; exact check_stage0)

/-- **The source stage of `Events` at every value**: the same calls with any value below `2 ^ 256`: `transfer` is not payable, and both sides revert with empty data. -/
theorem loweringValue (o : SolarTV.Machine.Oracle) (henv : Generic.CallerOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Events.stage0 (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) := by
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

#print axioms lowering

#print axioms loweringValue

end SolidCore.Refinement.Solar.Events
