import Verify.Tactic
import SolidCore.Refinement.Wide.Refines
import SolidCore.Refinement.KernelCopies
import SolidCore.Refinement.KernelRfl
import SolidCore.Refinement.Solar.Counter.Source

/-!
# counter: `inc(uint256 d)` adds `d` to the storage word `x`, or panics on overflow

The contract (scripts/refinement/counter/counter.sol; solar-tv/milestone/counter/counter.sol in
solar's tree, the same file),

    contract Counter { uint256 x; function inc(uint256 d) external { x += d; }
      function get() external view returns (uint256) { return x; } }

compiled by solar with `-Ogas --evm-version osaka` to the 83 bytes of runtime bytecode `code`.

* SolidCore's checked contract is `contract?`, the type checker on
  `Source.Counter.importedSourceUnit`. The kernel checks `shape_eq` (`kernel_rfl`): that its
  core is `coreLit` and that its constructor leaves no storage and no logs, by one conversion
  check on copies of the type checker that read the selectors from a table (`selector_eq`,
  each selector checked by Keccak-256 on its own).
* `model` is `inc` as a Loom program over the storage: it reads slot 0, panics with
  `Panic(0x11)` when `x + d` does not fit in 256 bits, and otherwise writes `x + d` to slot 0.
  It is stated for every storage; `run_inc` ties it to SolidCore on every argument word from the
  deployed (empty) storage by symbolic evaluation of the interpreter (`wide_symex`).
* `scope` is every call of `inc` with any argument word below `2 ^ 256`, no value, from the
  deployed storage. There `x = 0`, so `x + d` always fits and the call stores `d`: `post`.
  The overflow branch of the model, and `get`, are outside the scope.

Nothing here uses `native_decide` or `bv_decide`.
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Verify

/-- The interpreter fuel. -/
def fuel : Nat := 4096

/-- solar's runtime bytecode of `Counter` (compiler sources of the commit the manifest names,
`-Ogas --evm-version osaka`), as hex. -/
def runtimeHex : String :=
  "346034575f3560e01c80636d4ce63c146038578063812600df03603457602436106034575f5460043581019081106041575f55005b5f5ffd5b5f545f5260205ff35b6011602052634e487b715f526024601cfd"

/-- The SHA-256 of the runtime bytecode. -/
def runtimeSha256 : String := "daed21b0c790bb2c08bcf999c9ebc6fea950c213ea0a799418552aa14c18f6ec"

/-- The runtime bytecode read big-endian. -/
def runtimeNat : Nat :=
  0x346034575f3560e01c80636d4ce63c146038578063812600df03603457602436106034575f5460043581019081106041575f55005b5f5ffd5b5f545f5260205ff35b6011602052634e487b715f526024601cfd

/-- The runtime bytecode's length in bytes. -/
def runtimeSize : Nat := 83

/-- solar's runtime bytecode of `Counter`. -/
def code : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat runtimeNat runtimeSize

/-- The selector of `inc(uint256)`. -/
def incSelector : Nat := 0x812600df

/-- The selector of `get()`. -/
def getSelector : Nat := 0x6d4ce63c

/-- SolidCore's checked `Counter`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.Counter.importedSourceUnit "Counter"

/-- The function of the scope, `inc`, and its parameter. -/
def fns : List Fn := [⟨incSelector, [(.uint 256)]⟩]

/-- SolidCore's core contract of `Counter`, as the type checker leaves it. -/
def coreLit : Contract :=
  { storageFields := [{ name := "x",
                        slot := 0,
                        ty? := some (SolidCore.Solidity.Source.Ty.uint256),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.uint256)),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 32,
                        packedSigned := false }],
    immutableFields := [],
    eventDecls := [],
    errorDecls := [],
    functions := [{ name := "inc",
                    selector? := some 2166751455,
                    payable := false,
                    params := [{ name := "d", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "d")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "d")),
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "x"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "d"))]],
                    dispatchId? := none },
                  { name := "get",
                    selector? := some 1833756220,
                    payable := false,
                    params := [],
                    paramAbiCleanups := [],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.ref)
                                         "x"
                                         [])]]],
                    dispatchId? := none },
                  { name := "__internal_inc(uint256)#[SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "d", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "d")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "d")),
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "x"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "d"))]],
                    dispatchId? := none },
                  { name := "__internal_get()#[]",
                    selector? := none,
                    payable := false,
                    params := [],
                    paramAbiCleanups := [],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.ref)
                                         "x"
                                         [])]]],
                    dispatchId? := none }] }

/-! ## The selectors

The type checker computes each external function's selector by Keccak-256 of its
signature, which costs the kernel about 400 MB a hash. Each is checked once, alone, and the
shape check below runs on copies that read them from `selectorTable` (`selector_eq`). -/

/-- `inc`'s selector, by Keccak-256 of its signature. -/
def selInc : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "inc(uint256)"

kernel_rfl selInc_eq selInc incSelector

/-- `get`'s selector, by Keccak-256 of its signature. -/
def selGet : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "get()"

kernel_rfl selGet_eq selGet getSelector

/-- `ABI.selectorFromSignature`, with `Counter`'s signatures by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "inc(uint256)" then incSelector
  else if s = "get()" then getSelector
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  by_cases h0 : s = "inc(uint256)"
  · rw [ite_eq_left h0, h0]
    exact selInc_eq
  rw [ite_eq_right h0]
  by_cases h1 : s = "get()"
  · rw [ite_eq_left h1, h1]
    exact selGet_eq
  rw [ite_eq_right h1]

/-- SolidCore's checked core of `Counter`, the storage its constructor leaves and whether it
leaves no storage and no logs, when `Counter` type checks. -/
def shape? : Option (Contract × Option (List (Nat × Nat)) × Bool) :=
  match contract? with
  | .ok c => some (c.core, deployedStorage fuel c, deployedEmpty fuel c)
  | .error _ => none

-- `shape_eq : shape? = some (coreLit, some [], true)`: `Counter` type checks, its core is
-- `coreLit` and its constructor leaves no storage and no logs, by the kernel's conversion check
-- on the copy of `shape?` that reads the selectors from `selectorTable` (`selector_eq`): one
-- check evaluates the type checker once and hashes nothing (`SolidCore.Refinement.KernelRfl`).
kernel_rfl shape_eq shape? (some (coreLit, some [], true)) using selector_eq

/-- The checked contract has the core `coreLit`, and its constructor leaves no storage and no
logs. -/
theorem shape_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core = coreLit ∧ deployedStorage fuel c = some [] ∧ deployedEmpty fuel c = true := by
  have h := shape_eq
  unfold shape? at h
  rw [hc] at h
  obtain ⟨hk, h⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hs, he⟩ := Prod.mk.inj h
  exact ⟨hk, hs, he⟩

/-- `Counter` type checks. -/
theorem contract_ok : ∃ c, contract? = .ok c := by
  have h := shape_eq
  unfold shape? at h
  cases hc : contract? with
  | ok c => exact ⟨c, rfl⟩
  | error _ => rw [hc] at h; simp at h

/-- `inc` as a Loom program over the storage. -/
def model (ws : List Nat) : SolM (List Nat) := do
  let x ← sload 0
  if x + ws.getD 0 0 < 2 ^ 256 then do
    sstore 0 (x + ws.getD 0 0)
    pure []
  else revert (panic 0x11)

/-- What a call of `inc(d)` from empty storage shows: success, no output, no logs, and slot 0
holding `d`. -/
def expected (d : U256) : Observable :=
  { success := true, output := [], logs := [],
    storage := fun slot => if slot % 2 ^ 256 = 0 then d.toNat else 0 }

theorem observe_model (d : U256) :
    observe (fun _ => 0) (model [d.toNat] (fun _ => 0)) = expected d := by
  have hd := d.isLt
  simp only [model, sload, sstore, bind, StateT.bind, pure, StateT.pure, Except.bind,
    Except.pure, List.getD_cons_zero, Nat.zero_add, hd, ↓reduceIte, observe, expected,
    Nat.zero_mod, Nat.mod_eq_of_lt hd]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs `inc` on any argument word, from the deployed storage, to `expected d`. -/
theorem run_inc {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) (w : U256) :
    Source.run fuel c (callOf incSelector [w]) = some (expected w) := by
  rw [run_eq hd]
  have hs := hd.storage
  have hev := hd.events
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, incSelector, get?_insert]
  case pos =>
    rename_i hp
    exfalso
    have hw := w.isLt
    simp only [getElem?_of_isEmpty hs, Nat.zero_mod, Nat.zero_add] at hp
    omega
  case h_1 =>
    rename_i heq
    simp [getElem?_of_isEmpty hs] at heq
  case h_2 =>
    simp [Source.observe, expected, State.logEntries, State.loadSlot, StorageMap.lookup?]
    funext slot
    simp only [Std.HashMap.getElem?_insert, Shared.norm, Shared.wordModulus, beq_iff_eq]
    try rw [show EvmYul.UInt256.size = 2 ^ 256 from rfl]
    simp only [Nat.reducePow]
    by_cases h : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0
    · simp [h]
    · have h' : ¬0 = slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := fun e => h e.symm
      simp [h, h', getElem?_of_isEmpty hs]

/-- Every call of `inc` on any argument word, with no value, from the deployed (empty)
storage. -/
def scope : Call → Prop := fullScope fns []

/-- No precondition beyond the scope. -/
def pre : Call → Prop := fun _ => True

/-- `inc(d)` from the storage `σ` with slot 0 holding `x`: when `x + d` fits in 256 bits, the
call succeeds with no output and leaves slot 0 holding `x + d` and every other slot as it was;
otherwise it reverts with `Panic(0x11)` and the storage stays `σ`. It never logs. -/
def post (call : Call) (obs : Observable) : Prop :=
  let d := (argWords 1 call).getD 0 0
  let x := slotValue call.storage 0
  obs.logs = [] ∧
    if x + d < 2 ^ 256 then
      obs.success = true ∧ obs.output = [] ∧
        ∀ slot, obs.storage slot = if slot % 2 ^ 256 = 0 then x + d else slotValue call.storage slot
    else
      obs.success = false ∧ obs.output = panic 0x11 ∧
        ∀ slot, obs.storage slot = slotValue call.storage slot

theorem scope_callOf {call : Call} (h : scope call) : ∃ d : U256, call = callOf incSelector [d] := by
  obtain ⟨fn, hfn, args, hlen, hlt, rfl⟩ := h
  simp only [fns, List.mem_singleton] at hfn
  subst hfn
  match args, hlen with
  | [a], _ =>
    refine ⟨BitVec.ofNat 256 a, ?_⟩
    have ha' : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (hlt a (by simp))
    simp only [callOf, List.map_cons, List.map_nil, BitVec.toNat_ofNat, ha']

theorem slotValue_nil : slotValue [] = fun _ => 0 := rfl

/-- `model` implements SolidCore's `Counter` on every call of the scope. -/
theorem implements {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : Deployed fuel c d) : Implements fuel c scope (argWords 1) model :=
  implements_of_run' (by simp [fns]) fun fn hfn ws hl => by
    simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
    subst hfn
    rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hl
    rw [slotValue_nil, List.map_singleton, observe_model]
    exact run_inc hcore hd w

/-- SolidCore runs `inc` on any argument word to `expected d`, from its checked contract. -/
theorem source_run {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (w : U256) :
    Source.run fuel c (callOf incSelector [w]) = some (expected w) := by
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact run_inc hk hd w

theorem argWords_inc (d : U256) : argWords 1 (callOf incSelector [d]) = [d.toNat] := by
  have := argWords_calldata incSelector [d.toNat] (by simp [d.isLt]) 0 []
  simpa [callOf] using this

/-- The verification conditions of `inc`, by Loom's weakest preconditions: `vcs_of_fullScope`
and the `wp` rules of `Verify.Basic`, as `sc_vcgen` applies them, then `simp` on the slots. -/
theorem vcs : ∀ call, scope call → pre call → vc model (argWords 1) post call := by
  refine vcs_of_fullScope (by simp [fns]) ?_
  intro fn hfn call args hcall hw hlen hargs hinit hpre
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  subst fn hcall
  rcases args with _ | ⟨a, _ | _⟩ <;> simp at hlen
  have ha : a < 2 ^ 256 := hargs a (by simp)
  simp only [model, post, hw, wp_bind, wp_pure, wp_sload, wp_sstore, wp_revert, wp_ite,
    List.getD_cons_zero, slotValue, List.foldl_nil, Nat.zero_add, ha, ↓reduceIte, Nat.zero_mod,
    Nat.mod_eq_of_lt ha]
  simp

/-- **The specification of Counter's `inc`**, as a triple against SolidCore, from `model`'s
weakest precondition (`vcs`) and `implements`. -/
theorem spec : ∃ c, contract? = .ok c ∧ Triple fuel c scope pre post := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact ⟨c, hc, triple_of_wp (implements hk hd) vcs⟩

/-- The specification of Counter's `inc` as `Satisfies` on SolidCore. -/
theorem satisfies : ∃ c, contract? = .ok c ∧ Satisfies (solidCore fuel) c scope pre post := by
  obtain ⟨c, hc, h⟩ := spec
  exact ⟨c, hc, satisfies_of_triple h⟩

/-- info: 'SolidCore.Refinement.Solar.Counter.satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms satisfies

/-- info: 'SolidCore.Refinement.Solar.Counter.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_run

end SolidCore.Refinement.Solar.Counter
