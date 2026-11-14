import Verify.ShapeOpen
import Verify.Spec.TreeMapNested

/-!
# UniswapV2Pair: the reviewed inputs of the published statement

The valid calls, the admitted environments and worlds, the named premise, the allowed statuses
and the specification's call context and ghost step (Statement.lean says what each means). This
module imports neither the export nor any proof, so a driver-written statement can import it as a
spec module (tools/certify/final.py, kind open_functional).
-/

namespace SolidCore.Spec.UniswapV2.PairSpec

open SolarTV SolidCore.Refinement SolidCore.Refinement.Shapes

/-! ## The calls -/

/-- `swap(uint256,uint256,address,bytes)`. -/
abbrev swapSel : Nat := 0x022c0d9f
/-- `skim(address)`. -/
abbrev skimSel : Nat := 0xbc25cf77
/-- `sync()`. -/
abbrev syncSel : Nat := 0xfff6cae9

/-- `n` as a 32-byte big-endian word. -/
def word (n : Nat) : List Nat := (EthLib.Base.natToBytes 32 n).map (·.toNat)

/-- The call data of `swap(a0, a1, to, data)` as solc's encoder writes it: the head, the offset
`0x80`, the length and the data padded to whole words. -/
def swapData (a0 a1 dst : Nat) (data : List Nat) : List Nat :=
  (EthLib.Base.natToBytes 4 swapSel).map (·.toNat) ++ word a0 ++ word a1 ++ word dst ++ word 0x80 ++
    word data.length ++ data ++ List.replicate ((32 - data.length % 32) % 32) 0

/-- A call with call data `d` from the storage `σ`, without value. -/
def mkCall (d : List Nat) (σ : List (Nat × Nat)) : Call :=
  { calldata := ⟨(d.map UInt8.ofNat).toArray⟩, callvalue := 0, storage := σ }

/-- The valid calls of `swap`. -/
def ValidSwap (call : Call) : Prop :=
  ∃ σ a0 a1 dst data, a0 < 2 ^ 256 ∧ a1 < 2 ^ 256 ∧ dst < 2 ^ 160 ∧ data.length < 2 ^ 32 ∧
    (∀ b ∈ data, b < 256) ∧ call = mkCall (swapData a0 a1 dst data) σ

/-- The valid calls of `skim`. -/
def ValidSkim (call : Call) : Prop :=
  ∃ σ dst, dst < 2 ^ 160 ∧ call = mkCall ((EthLib.Base.natToBytes 4 skimSel).map (·.toNat) ++ word dst) σ

/-- The valid calls of `sync`. -/
def ValidSync (call : Call) : Prop :=
  ∃ σ, call = mkCall ((EthLib.Base.natToBytes 4 syncSel).map (·.toNat)) σ

/-- The statement's valid calls. -/
def Valid (call : Call) : Prop := ValidSwap call ∨ ValidSkim call ∨ ValidSync call

/-! ## The environment -/

/-- The admitted bytecode environments. -/
def EnvOk (env : TargetEnv) : Prop := env.WF

/-- The source worlds a result of the bytes may be explained by: open worlds (every call
answered), return data below `2 ^ 64` bytes, account code at addresses below `2 ^ 160`. -/
def Wide (W : World) : Prop :=
  W.Open ∧ (∀ p ∈ W.codes.getD [], p.1 < 2 ^ 160) ∧
    (∀ h world request a, W.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 64)

open SolidCore.Solidity.Source in
/-- The pair's storage in an open world, as SolidCore adopts it after a call (`adoptWorld`). -/
def selfStorage (w : SolidCore.Solidity.Shared.OpenWorld) : List (Nat × Nat) :=
  ((w.accounts.find? (wordToAddress selfAddress)).getD default).storage.toList.map
    fun kv => (u256ToWord kv.1, u256ToWord kv.2)

/-- **No reentrant state change**: every answer to an external call leaves the pair's storage as
it was sent. A token or callee that calls back into the pair's unlocked ERC20 functions and
changes its storage during swap, skim or sync is outside the admitted worlds; such a result of the
bytes is reported as `Unadmitted`, not as meeting the specification. -/
def PairFramed (W : World) : Prop :=
  ∀ h world request a, W.ans h (.external world (.call request)) = some a →
    slotValue (selfStorage a.postWorld) = slotValue (selfStorage world)

/-- The admitted source worlds: the wide ones without reentrant state change. -/
def Admit (W : World) : Prop := Wide W ∧ PairFramed W

/-- The storage word of `balanceOf[address(0)]` (slot 1), as the specification computes it. -/
def zeroBalanceSlot : Nat :=
  SolidCore.Spec.keccakWord (SolidCore.Spec.wordBytes 0 ++ SolidCore.Spec.wordBytes 1)

/-- The storage word of `allowance[address(0)][s]` (slot 2), as the specification computes it. -/
def zeroAllowanceSlot (s : Nat) : Nat :=
  SolidCore.Spec.keccakWord (SolidCore.Spec.wordBytes s ++
    SolidCore.Spec.wordBytes (SolidCore.Spec.keccakWord (SolidCore.Spec.wordBytes 0 ++ SolidCore.Spec.wordBytes 2)))

/-- **The named premise, scoped to the hashes the statement reads.** swap, skim and sync write
only the pair's fixed slots (below 13: reserves 8, price accumulators 9 and 10, the lock 12), and
the specification reads through keccak only the ERC20 invariants' words `balanceOf[address(0)]`
and `allowance[address(0)][s]`. The premise says none of those words is a fixed slot. It is not an
injectivity assumption: no two hashes need differ, so the counting argument that refutes
`NestedSlotsSeparated` (2^320 preimages into 2^256 words) does not apply; it asks 2^160 + 1
keccak outputs to avoid 13 values. Not proved (it is a fact about keccak256 the kernel cannot
compute for every address); a premise of the statement, never an axiom. To be replaced by the
footprint-scoped premise of Verify/Spec/HashScope.lean (`ScopedSep`). -/
def HashScope : Prop :=
  13 ≤ zeroBalanceSlot % 2 ^ 256 ∧ ∀ s, s < 2 ^ 160 → 13 ≤ zeroAllowanceSlot s % 2 ^ 256

/-! ## Allowed statuses and the specification -/

/-- **The allowed statuses: every status.** swap, skim and sync bubble a callee's revert data
verbatim (the tokens' `balanceOf` and the `uniswapV2Call` callback are high-level calls), and an
admitted world may revert with any data, so no revert data can be excluded: termination is stated
with any status, and an arbitrary revert is not counted as functional success (`Post` constrains
successes only). Recorded as the statement's declared vacuity of the allowed statuses. -/
def Allowed (_W : World) (_call : Call) (_obs : Observable) : Prop := True

/-- The call context of the specification: the statement's caller and contract, its block. -/
def ctxOf (call : Call) : SolidCore.Spec.Ctx :=
  { sender := callerAddress, value := call.callvalue, timestamp := 1, self := selfAddress }

/-- swap, skim and sync update no ghost. -/
def idStep : SolidCore.Spec.GhostStep := fun _ g => g

end SolidCore.Spec.UniswapV2.PairSpec
