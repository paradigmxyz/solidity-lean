import SolidCore.Refinement.Generic.SourceRun
import SolidCore.Refinement.Generic.MirRun
import SolidCore.Refinement.Generic.Simp
import SolidCore.Refinement.Compose
import SolidCore.Refinement.Evm.Calldata

/-!
# The generic source stage: SolidCore to solar's first lowered MIR

`stageAt` is one theorem for every contract of the fragment: given SolidCore's checked contract
`c`, whose constructor leaves the storage entries `s` and no logs, and a lowered MIR module `m`
(solar's module after `lower-evm-shaped`, so with lower-abi's decoding and lower-dispatch's
dispatcher), if the kernel's evaluation of `check fuel mirFuel c.core m fns` is `true`, then

    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c m
      (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call)

under every oracle `o`: on every call of a function of `fns` on any argument words below
`2 ^ 256`, with no value, from any storage that writes every slot the constructor wrote, `m`
shows what SolidCore shows, its logs included. `stageDeployed` is the case of the deployed
storage itself, and `stage` the case of a constructor that leaves no storage, from any storage.

The symbolic run of `m` reads the oracle's caller and Keccak-256 only with the environment flags
(`EnvFlags`; `check ... .all`), which a module that reads `msg.sender` or a mapping needs.
`stageAtEnv`, `stageDeployedEnv` and `stageEnv` are the same stages for that check, under every
oracle that `SourceEnvOk` describes: its caller is SolidCore's `callerAddress` (`CallerOk`), and
its Keccak-256 of the 64 bytes of two words is SolidCore's slot hash `solHash` of them
(`HashOk`). `stageAtCaller` and `stageCaller` are the stages for `check ... .callerOnly`, for a
module that reads the caller and hashes nothing, under every oracle with SolidCore's caller.
Nothing else of the oracle is assumed.

The fragment is what `eraseFn` and `symTree` accept: parameters that are unsigned words of
`0 < b ≤ 256` bits or addresses (a dirty argument word reverts), `uint256`-word returns, checked
`+`, `-`, `*` with narrow cleanups, truncating casts such as `uint256(a)`, bitwise `&`, `|`, `^`,
comparisons, scoped locals, `msg.sender`, unsigned storage fields alone in their slot or packed
with others and mappings to `uint256` (reads, writes and compound assignments such as `v += x` and
`w ^= x`), `if`, blocks, returns and reverts with `Panic`, and the other statements `eraseStmt`
erases, dispatched by selector with static call data. `check` asks, for each function of `fns`, that its selector fits in four bytes,
that SolidCore dispatches it to a function with that many parameters, and that the two trees
agree: the erasure of the SolidCore function in the contract's `envOf` and the symbolic run of
the MIR module on its selector, compared by `=` on their canonical forms (`Tree.canonWith solHash`:
`Tree.canon`, with the hash of two constants folded by SolidCore's slot hash).

The proof joins the two halves: `source_run` (SolidCore runs the call as the erased tree, with
the call's argument words, storage and `solHash`) and `symTree_sound` (the module runs the call as
its symbolic tree), with `callFacts` giving the symbolic run's facts about the call data, and
`Tree.eval_canonWith` the agreement of the trees, on calls whose hash is `solHash` as both halves'
are.

`calldataWord_eq` and its two helpers are Solar.W1's, restated here so that the generic stage
does not depend on a milestone's artifacts.
-/

namespace SolidCore.Refinement.Generic
open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm

/-! ## The call data the symbolic run reads -/

theorem shl_or_ofNat (acc b : Nat) (hb : b < 256) :
    (BitVec.ofNat 256 acc <<< 8) ||| BitVec.ofNat 256 b = BitVec.ofNat 256 (acc * 256 + b) := by
  have hand : (BitVec.ofNat 256 acc <<< 8) &&& BitVec.ofNat 256 b = 0 := by
    ext i hi
    rw [BitVec.getElem_and, BitVec.getElem_shiftLeft, ← BitVec.getLsbD_eq_getElem,
      ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
    by_cases h8 : i < 8
    · simp [h8]
    · have : b.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb
          (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt h8)))
      simp [BitVec.getLsbD_ofNat, this]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem foldl_word (data : ByteArray) (off : Nat) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun (acc : BitVec 256) i =>
        (acc <<< 8) ||| BitVec.ofNat 256 (data.data.getD (off + i) 0).toNat)
        (BitVec.ofNat 256 acc) =
      BitVec.ofNat 256 (l.foldl (fun acc i => acc * 256 + (byteAt data (off + i)).toNat) acc)
  | [], _ => rfl
  | i :: l, acc => by
    simp only [List.foldl_cons]
    have hget : (data.data.getD (off + i) 0) = byteAt data (off + i) := rfl
    rw [hget, shl_or_ofNat _ _ (byteAt data (off + i)).toNat_lt, foldl_word data off l]

/-- CALLDATALOAD in SolarTV is EthLib's: the big-endian word of 32 bytes of call data from the
offset, zero past its end. -/
theorem calldataWord_eq (call : Call) (off : BitVec 256) :
    calldataWord call off = loadWord call.calldata off.toNat 32 := by
  unfold calldataWord loadWord bufferRead bytesToNat
  rw [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, foldl_word, List.foldl_map]

/-- The call of selector `sel` on the argument words `args` from the storage `σ` gives the
symbolic run its facts, with the argument words, the storage and SolidCore's slot hash
`⟨args, slotValue σ, solHash⟩`. -/
theorem callFacts (sel : Nat) (hsel : sel < 2 ^ 32) (args : List Nat)
    (hargs : ∀ a ∈ args, a < 2 ^ 256) (σ : List (Nat × Nat)) :
    CallFacts sel args.length ⟨args, slotValue σ, solHash⟩
      { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } := by
  have hcd := calldata_eq_cdOf sel args hargs
  refine ⟨rfl, ?_, ?_, ?_, rfl, slotValue_store σ⟩
  · show (Abi.calldata sel args).size = _
    rw [hcd, size_cdOf, size_selectorOf]
    simp
  · intro i hi hw
    rw [calldataWord_eq]
    show (loadWord (Abi.calldata sel args) _ 32).toNat = _
    rw [hcd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
    rw [loadWord_cdOf_getD _ _ _ (by simp [size_selectorOf]) (by simp [size_selectorOf])
      (by simp [size_selectorOf]; omega)]
    simp only [size_selectorOf, show 4 + 32 * i - 4 = 32 * i by omega,
      show 32 * i / 32 = i by omega, WExpr.eval]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · rw [calldataWord_eq]
    show EvmRules.Evm.shr 224 (loadWord (Abi.calldata sel args) _ 32) = _
    rw [hcd]
    have := shr_cdOf_selectorOf sel (args.map (BitVec.ofNat 256)) hsel
    simpa [EvmRules.Evm.shr, bitwiseShr] using this

/-! ## The oracle's environment -/

/-- The oracle's caller is SolidCore's `callerAddress`, `callerWord`. -/
def CallerOk (o : Oracle) : Prop := (o.caller.setWidth 256).toNat = callerWord

/-- The oracle's Keccak-256 of the 64 bytes of two words is SolidCore's slot hash of them, the
hash of the same bytes. -/
def HashOk (o : Oracle) : Prop :=
  ∀ a b, a < 2 ^ 256 → b < 2 ^ 256 → (o.keccak (wordBytes a ++ wordBytes b)).toNat = solHash a b % 2 ^ 256

/-- What the stages with the environment flag ask of the oracle: `CallerOk` and `HashOk`. -/
structure SourceEnvOk (o : Oracle) : Prop where
  caller : CallerOk o
  hash : HashOk o

/-- An oracle `SourceEnvOk` describes is one the symbolic run with the environment flag takes, for
every call whose hash is `solHash`. -/
theorem SourceEnvOk.envOk {o : Oracle} (h : SourceEnvOk o) (args : List Nat) (store : Nat → Nat) :
    EnvOk o ⟨args, store, solHash⟩ :=
  ⟨h.caller, h.hash⟩

/-- What the flags `env` ask of the oracle: SolidCore's caller when they read the caller, and
SolidCore's hash of two words when they hash. -/
structure SourceAsk (env : EnvFlags) (o : Oracle) : Prop where
  caller : env.caller = true → CallerOk o
  hash : env.hash = true → HashOk o

/-- The flags off ask nothing. -/
theorem SourceAsk.off {o : Oracle} : SourceAsk .off o :=
  ⟨fun h => by simp [EnvFlags.off] at h, fun h => by simp [EnvFlags.off] at h⟩

/-- An oracle `SourceEnvOk` describes gives every flag what it asks. -/
theorem SourceEnvOk.ask {o : Oracle} (h : SourceEnvOk o) {env : EnvFlags} : SourceAsk env o :=
  ⟨fun _ => h.caller, fun _ => h.hash⟩

/-- An oracle with SolidCore's caller gives the caller-only flags what they ask. -/
theorem CallerOk.ask {o : Oracle} (h : CallerOk o) : SourceAsk .callerOnly o :=
  ⟨fun _ => h, fun h => by simp [EnvFlags.callerOnly] at h⟩

/-- What the flags ask of the oracle, for the symbolic run on a call whose hash is `solHash`. -/
theorem SourceAsk.envAsk {env : EnvFlags} {o : Oracle} (h : SourceAsk env o) (args : List Nat)
    (store : Nat → Nat) : EnvAsk env o ⟨args, store, solHash⟩ :=
  ⟨h.caller, h.hash⟩

/-! ## The check and the stage -/

/-- Whether the function of `fns` with selector `f.sel` lowers to `m`: SolidCore dispatches the
selector to a function with `f`'s parameter count, and its erased tree and the symbolic run of
`m` on the selector, with `mirFuel` blocks along each path and the environment flag `env`, agree in
canonical form. -/
def checkFn (fuel mirFuel : Nat) (core : Contract) (m : Module) (env : EnvFlags) (f : Fn) : Bool :=
  decide (f.sel < 2 ^ 32) &&
    match core.findFunctionBySelector? f.sel with
    | none => false
    | some fn =>
      decide (fn.params.length = f.params.length) &&
        match eraseFn (envOf core) fuel fn, symTree m f.sel f.params.length mirFuel env with
        | some t1, some t2 => decide (t1.canonWith solHash = t2.canonWith solHash)
        | _, _ => false

/-- Whether every function of `fns` lowers to `m`, with the environment flag `env` (off by
default). -/
def check (fuel mirFuel : Nat) (core : Contract) (m : Module) (fns : List Fn) (env : EnvFlags := .off) :
    Bool :=
  fns.all (checkFn fuel mirFuel core m env)

/-- The generic source stage for `check` with the environment flag `env`, under every oracle when
the flag is off and every oracle `SourceEnvOk` describes when it is on. -/
theorem stageAtWith (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : check fuel mirFuel c.core m fns env = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) := by
  rintro _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  have hcf := List.all_eq_true.mp hchk f hf
  unfold checkFn at hcf
  cases hfind : c.core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht1 : eraseFn (envOf c.core) fuel fn with
  | none => simp [hfind, ht1] at hcf
  | some t1 =>
  cases ht2 : symTree m f.sel f.params.length mirFuel env with
  | none => simp [hfind, ht1, ht2] at hcf
  | some t2 =>
  simp only [hfind, ht1, ht2, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hpl, hcf⟩ := hcf
  have hsrc := source_run hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) hargs
  change Source.run fuel c _ = some obs at hrun
  rw [hsrc] at hrun
  cases hrun
  rw [← hlen] at ht2
  rw [symTree_sound (callFacts f.sel hsel args hargs σ) o m (henv.envAsk _ _) ht2,
    ← Tree.eval_canonWith rfl, ← hcf, Tree.eval_canonWith rfl]

/-- **The generic source stage**: a checked contract whose constructor leaves the storage entries
`s` and no logs and a lowered MIR module that `check` accepts give the stage from SolidCore to the
module's lowered MIR semantics, under every oracle, on every call of a function of `fns` on any
argument words below `2 ^ 256`, with no value, from any storage that writes every slot of `s`. -/
theorem stageAt (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module}
    {fns : List Fn} (hchk : check fuel mirFuel c.core m fns = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  stageAtWith o hd (env := .off) SourceAsk.off hchk

/-- The generic source stage from the deployed storage `s`. -/
theorem stageDeployed (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} (hchk : check fuel mirFuel c.core m fns = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fullScope fns s) :=
  SolarTV.Stage.mono (stageAt o hd hchk) fun _ h => ⟨s, fun kv hkv => ⟨kv, hkv, rfl⟩, h⟩

/-- The generic source stage for a contract whose constructor leaves no storage, from any
storage. -/
theorem stage (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, fullScope fns σ call) :=
  SolarTV.Stage.mono (stageAt o hd hchk) fun _ ⟨σ, h⟩ =>
    ⟨σ, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

/-- **The generic source stage with the environment flag**: `stageAt` for a module that
`check ... true` accepts, which may read the caller and hash two words, under every oracle whose
caller is `callerWord` and whose Keccak-256 of two words is `solHash` (`SourceEnvOk`). -/
theorem stageAtEnv (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .all = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  stageAtWith o hd henv.ask hchk

/-- The generic source stage with the environment flag from the deployed storage `s`. -/
theorem stageDeployedEnv (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .all = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fullScope fns s) :=
  SolarTV.Stage.mono (stageAtEnv o henv hd hchk) fun _ h => ⟨s, fun kv hkv => ⟨kv, hkv, rfl⟩, h⟩

/-- The generic source stage with the environment flag for a contract whose constructor leaves no
storage, from any storage. -/
theorem stageEnv (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .all = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, fullScope fns σ call) :=
  SolarTV.Stage.mono (stageAtEnv o henv hd hchk) fun _ ⟨σ, h⟩ =>
    ⟨σ, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

/-- The generic source stage with the caller-only flags (a contract that reads `msg.sender` but
hashes nothing), from any storage that writes every slot of `s`, under every oracle with
SolidCore's caller. -/
theorem stageAtCaller (o : Oracle) (henv : CallerOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .callerOnly = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  stageAtWith o hd henv.ask hchk

/-- The caller-only stage for a contract whose constructor leaves no storage, from any storage. -/
theorem stageCaller (o : Oracle) (henv : CallerOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .callerOnly = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, fullScope fns σ call) :=
  SolarTV.Stage.mono (stageAtCaller o henv hd hchk) fun _ ⟨σ, h⟩ =>
    ⟨σ, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

end SolidCore.Refinement.Generic
