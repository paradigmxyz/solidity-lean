import Verify.Shapes
import Verify.Basic
import SolidCore.Refinement.Generic.Total
import SolidCore.Refinement.Solar.Totality
import SolidCore.Refinement.Solar.AssembleGasLoop
import SolidCore.Refinement.Solar.RunOracle
import SolidCore.Refinement.Keccak.TwoWords

/-!
# The certified shape of a loop-free contract, from the generic pieces

One theorem for every contract whose source stage is the generic check (`Generic.check`, with
`Generic.checkValue` for calls with a value) and whose bytecode the checker of code with loops
accepts (`AssembleLoop.checkL`, on a certificate `tools/certify/asm_cert.py` infers and the kernel's
evaluation re-derives). Its inputs are exactly the evidence the certify driver generates:

* a source stage and its definedness (from `Generic.check` and `Generic.checkValue`, by
  `Generic.stageAtValueWith` and `Generic.definedAtValue`);
* `backend`: solar-tv's stages from that module to the final EVM IR, under every oracle;
* `ends`: the final EVM IR ends within `N` blocks on every call (the last stage's fuel: each stage
  file runs both programs within a fuel the kernel's evaluation reaches);
* `asm`: `checkL` accepts the final EVM IR against the exact bytecode.

From these, at the one oracle `oracle` (EthLib's caller, Keccak-256 and environment, as the
bytecode's own run reads them; `oracle_ok`), `compiled_of` proves `Compiled`:

* equivalence (`Shapes.Equiv`, sharpened to `EquivG`): at every gas below `2 ^ 256`, every result
  of the bytecode on a valid call is SolidCore's, or a failure that changes nothing, and that only
  below the gas bound;
* termination: SolidCore ends on every valid call, with any status;
* resources: from `AssembleLoop.gasBoundL cert N` gas on, the bytecode gives exactly SolidCore's
  result, a revert with its data included (`AssembleLoop.stage_of_checkL_gas`).

`Compiled` has no specification: a contract with none never reaches `Shapes.Certified`.
`Compiled.certified` adds a specification proved of the same source semantics (`Allowed`, `Post`).

One fixed oracle suffices: the checker's fragment (no GAS, no calls, no return data) reads of the
oracle only the caller, the Keccak-256 of memory and the block and transaction words, all of which
are EthLib's in `oracle`; `within_of_checkL` and `forward_of_checkL` are theorems about EthLib's
run of the bytes, at every gas, related to the EVM IR under that oracle.
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Refinement.Solar SolidCore.Solidity

/-! ## Sharper equivalence and the status without a specification -/

/-- **Equivalence with the gas bound**: every result of the bytecode on a valid call, at every gas
below `2 ^ 256`, is the source's, or a failure that changes nothing at a gas below the bound. At
and above the bound it is the source's exactly, its revert data included. -/
def EquivG (S : Sem) (p : S.Prog) (code : ByteArray) (Valid : Call → Prop) (G : Call → Nat) :
    Prop :=
  ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → ∀ obs, Final.Target.runWith gas code call = some obs →
    S.run p call = some obs ∨ (Inert call obs ∧ gas < G call)

theorem equivG_of {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop} {G : Call → Nat}
    (he : Equiv S p code Valid) (hr : Resources S p code Valid G) : EquivG S p code Valid G := by
  intro gas hg call hc obs hrun
  by_cases hlt : gas < G call
  · rcases he gas hg call hc obs hrun with e | e
    · exact Or.inl e
    · exact Or.inr ⟨e, hlt⟩
  · left
    rw [← (hr call hc).2 gas (Nat.not_lt.mp hlt) hg]
    exact hrun

theorem EquivG.equiv {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {G : Call → Nat} (h : EquivG S p code Valid G) : Equiv S p code Valid :=
  fun gas hg call hc obs hrun => (h gas hg call hc obs hrun).imp id And.left

/-- **Translation without a specification**: equivalence with the gas bound, termination with
any status, and resources. Reported with the specification status "none", never as the
strongest status. -/
structure Compiled (S : Sem) (p : S.Prog) (code : ByteArray) (Valid : Call → Prop)
    (G : Call → Nat) : Prop where
  inhabited : ∃ call, Valid call
  equiv : EquivG S p code Valid G
  terminates : Terminates S p Valid (fun _ _ => True)
  resources : Resources S p code Valid G

/-- A specification of the same source semantics (allowed statuses and a postcondition of every
source result) makes a compiled contract certified. -/
theorem Compiled.certified {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {G : Call → Nat} {Allowed Post : Call → Observable → Prop} (h : Compiled S p code Valid G)
    (allowed : ∀ call, Valid call → ∀ obs, S.run p call = some obs → Allowed call obs)
    (meets : Meets S p Valid Post) : Certified S p code Valid Allowed Post G where
  inhabited := h.inhabited
  equiv := h.equiv.equiv
  terminates := fun call hc => by
    obtain ⟨obs, hs, -⟩ := h.terminates call hc
    exact ⟨obs, hs, allowed call hc obs hs⟩
  meets := meets
  resources := h.resources

/-- A larger bound below `2 ^ 64` keeps the shape. -/
theorem Compiled.mono_gas {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {G G' : Call → Nat} (h : Compiled S p code Valid G) (hle : ∀ call, G call ≤ G' call)
    (hlt : ∀ call, G' call < 2 ^ 64) : Compiled S p code Valid G' where
  inhabited := h.inhabited
  equiv := fun gas hg call hc obs hrun =>
    (h.equiv gas hg call hc obs hrun).imp id fun ⟨hi, hl⟩ => ⟨hi, Nat.lt_of_lt_of_le hl (hle call)⟩
  terminates := h.terminates
  resources := fun call hc =>
    ⟨hlt call, fun gas h1 h2 => (h.resources call hc).2 gas (Nat.le_trans (hle call) h1) h2⟩

/-- The strongest status also gives the sharper equivalence. -/
theorem Certified.equivG {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {G : Call → Nat}
    (h : Certified S p code Valid Allowed Post G) : EquivG S p code Valid G :=
  equivG_of h.equiv h.resources

/-! ## The oracle of the bytecode's own run -/

/-- EthLib's caller, Keccak-256 and environment reads; every other answer from the empty table. -/
def oracle : Machine.Oracle :=
  RunOracle.tableOracle (Assemble.envOracle (Assemble.ethOracle RunOracle.anyOracle)) {}

theorem oracle_ok : Assemble.OracleOk oracle ∧ Assemble.EnvOk oracle :=
  RunOracle.table_ok _ _

theorem callerAddress_word :
    (SolidCore.Refinement.Target.address SolidCore.Refinement.callerAddress).toU256.toNat =
      Generic.callerWord := by
  decide +kernel

/-- It is an oracle every generic source stage takes, whatever its environment flags. -/
theorem oracle_sourceEnvOk : Generic.SourceEnvOk oracle :=
  ⟨by unfold Generic.CallerOk; rw [oracle_ok.1.1]; exact callerAddress_word,
    fun a b _ _ => by rw [oracle_ok.1.2]; exact Keccak.ethKeccak_twoWords a b⟩

/-! ## The composition -/

/-- **The shape from a total source stage, the backend stages and the loop checker.** -/
theorem compiled_of {S : Sem} {p : S.Prog} {m : MIR.Lowered.moduleLayer.Prog}
    {q : Assemble.Program} {code : ByteArray} {Valid scope : Call → Prop} {c : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (inhabited : ∃ call, Valid call)
    (src : Stage S (mirSem oracle) p m Valid) (defined : Defined S p Valid)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, Valid call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code c mx = true)
    (hG : AssembleLoop.gasBoundL c N < 2 ^ 64) :
    Compiled S p code Valid (fun _ => AssembleLoop.gasBoundL c N) := by
  have total : ∀ call, Valid call → ∃ obs, S.run p call = some obs := fun call hc =>
    Option.isSome_iff_exists.mp (defined call hc)
  have stage : Stage S (evmirSem oracle) p q Valid :=
    src.trans (backend.mono hscope)
  have hequiv : Equiv S p code Valid :=
    equiv_of_runs (sem := evmirSem) (q := fun _ => q) (Ok := fun o => o = oracle) total
      (fun o ho => ho ▸ stage)
      (fun gas _ call _ => ⟨oracle, rfl,
        AssembleLoop.within_of_checkL asm oracle (fun _ => oracle_ok.1) _ gas
          (fun _ => oracle_ok.2)⟩)
  have hres : Resources S p code Valid (fun _ => AssembleLoop.gasBoundL c N) :=
    resources_of_forward (B := evmirSem oracle) (q := q) total stage fun call _ =>
      ⟨hG, fun _ h1 _ obs hrun =>
        AssembleLoop.stage_of_checkL_gas asm oracle (fun _ => oracle_ok.1)
          (fun _ => oracle_ok.2) call N (Option.isSome_iff_exists.mp (ends call)) h1 obs hrun⟩
  exact ⟨inhabited, equivG_of hequiv hres, fun call hc => by
    obtain ⟨obs, hs⟩ := total call hc
    exact ⟨obs, hs, trivial⟩, hres⟩

/-- The valid calls of a generic stage: a function of `fns` on argument words below `2 ^ 256`, any
value below `2 ^ 256`, from a storage that writes every slot the constructor wrote. -/
def genericValid (fns : List Fn) (s : List (Nat × Nat)) (call : Call) : Prop :=
  ∃ σ v, Generic.Covers s σ ∧ Generic.fullScopeValue fns σ v call

/-- **The shape of a generic-stage contract**: the generic check at every value, the backend stages,
the final EVM IR's fuel and the loop checker. -/
theorem compiled {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {m : MIR.Lowered.Module}
    {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (inhabited : ∃ call, genericValid fns s call)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, genericValid fns s call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) :
    Compiled (solidCore fuel) c code (genericValid fns s) (fun _ => AssembleLoop.gasBoundL cert N) :=
  compiled_of inhabited
    (Generic.stageAtValueWith oracle hd oracle_sourceEnvOk.ask hchk hval)
    (Generic.definedAtValue hd hchk hval) backend hscope ends asm hG

/-- A call of every generic stage's scope: the first function on zero words, no value, from the
constructor's storage. -/
theorem genericValid_inhabited (f : Fn) (fns : List Fn) (s : List (Nat × Nat)) :
    ∃ call, genericValid (f :: fns) s call :=
  ⟨_, s, 0, fun kv hkv => ⟨kv, hkv, rfl⟩, by decide, f, List.mem_cons_self,
    List.replicate f.params.length 0, List.length_replicate,
    fun a ha => by rw [(List.mem_replicate.mp ha).2]; decide, rfl⟩

/-- info: 'SolidCore.Refinement.Shapes.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiled

/-- info: 'SolidCore.Refinement.Shapes.Compiled.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Compiled.certified


/-! ## Calls without a value, and specifications from triples -/

/-- The valid calls of a generic stage without a value: a function of `fns` on argument words below
`2 ^ 256`, no value, from a storage that writes every slot the constructor wrote. -/
def genericValid0 (fns : List Fn) (s : List (Nat × Nat)) (call : Call) : Prop :=
  ∃ σ, Generic.Covers s σ ∧ fullScope fns σ call

/-- **The shape of a generic-stage contract on calls without a value.** -/
theorem compiled0 {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {m : MIR.Lowered.Module}
    {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (inhabited : ∃ call, genericValid0 fns s call)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, genericValid0 fns s call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) :
    Compiled (solidCore fuel) c code (genericValid0 fns s) (fun _ => AssembleLoop.gasBoundL cert N) :=
  compiled_of inhabited (Generic.stageAtWith oracle hd oracle_sourceEnvOk.ask hchk)
    (Generic.definedAt hd hchk) backend hscope ends asm hG

theorem genericValid0_inhabited (f : Fn) (fns : List Fn) (s : List (Nat × Nat)) :
    ∃ call, genericValid0 (f :: fns) s call :=
  ⟨_, s, fun kv hkv => ⟨kv, hkv, rfl⟩, f, List.mem_cons_self,
    List.replicate f.params.length 0, List.length_replicate,
    fun a ha => by rw [(List.mem_replicate.mp ha).2]; decide, rfl⟩

/-- A total-correctness triple of SolidCore on part of the valid calls is the specification
"on those calls, `post`" of every source result. -/
theorem meets_of_triple {fuel : Nat} {c : TypeCheck.CheckedContract} {Valid scope : Call → Prop}
    {post : Call → Observable → Prop} (ht : SolidCore.Verify.Triple fuel c scope (fun _ => True) post) :
    Meets (solidCore fuel) c Valid (fun call obs => scope call → post call obs) :=
  fun call _ obs hrun hs => (ht call hs trivial).2 obs hrun

theorem Meets.and {S : Sem} {p : S.Prog} {Valid : Call → Prop} {P Q : Call → Observable → Prop}
    (h1 : Meets S p Valid P) (h2 : Meets S p Valid Q) :
    Meets S p Valid (fun call obs => P call obs ∧ Q call obs) :=
  fun call hc obs hrun => ⟨h1 call hc obs hrun, h2 call hc obs hrun⟩

/-- info: 'SolidCore.Refinement.Shapes.compiled0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiled0


/-! ## Code with loops: a total first lowered MIR, the loop checker's backward theorem -/

/-- **Equivalence, termination and the specification of a program that ends on every valid call**,
whose results the bytecode refines at every gas (`AssembleLoop.within_of_checkL` composed with
cut-point stages read backwards), with the specification proved of the same program. Resources are
not part of it: a gas bound needs the final EVM IR's block count. -/
theorem functional_of {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} (inhabited : ∃ call, Valid call)
    (ends : ∀ call, Valid call → (S.run p call).isSome = true)
    (allowed : ∀ call, Valid call → ∀ obs, S.run p call = some obs → Allowed call obs)
    (within : ∀ gas, Within S (ethLibWith gas) p code Valid) (meets : Meets S p Valid Post) :
    Functional S p code Valid Allowed Post where
  inhabited := inhabited
  equiv := fun gas _ call hc obs hrun => within gas call hc obs hrun
  terminates := fun call hc => by
    obtain ⟨obs, hs⟩ := Option.isSome_iff_exists.mp (ends call hc)
    exact ⟨obs, hs, allowed call hc obs hs⟩
  meets := meets

end SolidCore.Refinement.Shapes
