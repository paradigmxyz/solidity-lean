import SolidCore.Spec.TrustedBase.Hypotheses

/-!
# Interface ensures from an exported interface spec

`InterfaceEnsures ens tr` (`Hypotheses.lean`) takes the interfaces' ensures as a predicate on a
request and its response. `ifaceEnsOf` builds that predicate from an interface's exported spec (a
`Bundle` whose `FnSpec`s are the interface's functions), with the meaning `Post` gives a function's
ensures: when the calldata selects a function of the interface (its selector, then clean argument
words of its parameter types) and the call returns clean words of its return types, its ensures
hold of those arguments and results. solar-verify trusts exactly this of every interface call that
returns; `--spec-check` samples it where the implementation is in the file.

`ctx` is the callee's environment and `st` the state its storage and ghost reads see: an interface's
ensures speak of its arguments and results, which these do not affect.
-/

namespace SolidCore.Spec.TrustedBase

open SolarTV SolidCore.Spec EvmCompiler.Simulation

/-- A byte array's bytes, as numbers. -/
def bytesOf (b : ByteArray) : List Nat := b.data.toList.map (·.toNat)

/-- **The ensures of interface `iface` on one call** (see the module doc). -/
def ifaceEnsOf (iface : Bundle) (ctx : Ctx) (st : State) (r : CallRequest) (a : CallResponse) :
    Prop :=
  ∀ fs ∈ iface.spec.specs, ∀ args rets,
    4 ≤ (bytesOf r.calldata).length →
    bytesWord ((bytesOf r.calldata).take 4) = fs.selector →
    decodeWords fs.params (words ((bytesOf r.calldata).drop 4)) = some args →
    decodeWords fs.rets (words (bytesOf a.returnData)) = some rets →
    iface.satAll fs.ensures (mkEnv ctx args rets st st)

/-- A call that fails owes no ensures, so `InterfaceEnsures` constrains only returning calls. -/
theorem interfaceEnsures_of_default' {iface : Bundle} {ctx : Ctx} {st : State}
    {tr : Interaction.Transcript} (h : DefaultCalls tr) :
    InterfaceEnsures (ifaceEnsOf iface ctx st) tr :=
  interfaceEnsures_of_default h

/-! ## Witnesses: an interface `one() returns (uint256)` that ensures `result == 1` -/

/-- `function one() external returns (uint256)`, selector `0x12345678`, ensuring `result == 1`. -/
def oneFn : FnSpec :=
  { name := "one", selector := 0x12345678, params := [], rets := [.uint 256], payable := false,
    requires := [], ensures := [.bin .eq (.ret 0) (.lit 1)], succeedsIf := [] }

/-- The interface with `one`. -/
def oneIface : Bundle :=
  { spec := { name := "IOne", fns := [], invariants := [], ghosts := [], specs := [oneFn] },
    fuel := 1 }

/-- The calldata of `one()`. -/
def oneCalldata : ByteArray := ⟨#[0x12, 0x34, 0x56, 0x78]⟩

/-- The 32-byte big-endian word `v < 256`. -/
def smallWord (v : UInt8) : ByteArray := ⟨(List.replicate 31 (0 : UInt8) ++ [v]).toArray⟩

/-- A call of `one()` that returns the word `v`. -/
def oneEx (v : UInt8) : Interaction.Exchange :=
  ⟨.external default (.call { staticReq with calldata := oneCalldata }),
    (CallResponse.mk true (smallWord v) default (EvmYul.UInt256.ofNat 0) : CallResponse)⟩

theorem oneCalldata_facts :
    4 ≤ (bytesOf oneCalldata).length ∧
    bytesWord ((bytesOf oneCalldata).take 4) = 0x12345678 ∧
    decodeWords [] (words ((bytesOf oneCalldata).drop 4)) = some [] := by
  decide

theorem decode_smallWord1 : decodeWords [.uint 256] (words (bytesOf (smallWord 1))) = some [1] := by
  decide

theorem decode_smallWord0 : decodeWords [.uint 256] (words (bytesOf (smallWord 0))) = some [0] := by
  decide

/-- **Satisfiable with a call that returns**: `one()` returning 1 meets the interface's ensures. -/
theorem interfaceEnsures_one (ctx : Ctx) (st : State) :
    InterfaceEnsures (ifaceEnsOf oneIface ctx st) [oneEx 1] := by
  intro c hc _ fs hfs args rets _ _ hargs hrets
  simp only [callsOf, oneEx, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  simp only [oneIface, List.mem_cons, List.not_mem_nil, or_false] at hfs
  subst hfs
  rw [show (oneFn.rets) = [.uint 256] from rfl, decode_smallWord1] at hrets
  cases hrets
  simp [Bundle.satAll, Bundle.sat, oneFn, eval, mkEnv, BinOp.apply, ofProp]

/-- **Not trivial**: `one()` returning 0 breaks it. -/
theorem not_interfaceEnsures_zero (ctx : Ctx) (st : State) :
    ¬ InterfaceEnsures (ifaceEnsOf oneIface ctx st) [oneEx 0] := by
  intro h
  obtain ⟨h4, hsel, hargs⟩ := oneCalldata_facts
  have := h (default, { staticReq with calldata := oneCalldata },
    CallResponse.mk true (smallWord 0) default (EvmYul.UInt256.ofNat 0)) (by simp [callsOf, oneEx])
    rfl oneFn (by simp [oneIface]) [] [0] h4 hsel hargs decode_smallWord0
  simp [Bundle.satAll, Bundle.sat, oneFn, eval, mkEnv, BinOp.apply, ofProp] at this

end SolidCore.Spec.TrustedBase
