import Examples.C4.Spec.Export
import Examples.C4.Spec.ExportWrong
import Verify.Spec.TrustedBase
import Verify.C4
import SolidCore.Refinement.Corpus.C4
import SolidCore.Refinement.Spec

/-!
# c4: solar-verify's spec, proved of SolidCore and of solar's bytecode

c4 (`scripts/refinement/corpus/c4.sol`) with specs written for solar-verify
(`scripts/refinement/spec/c4.sol`):

    contract Main {
        uint8 v;
        uint8 w = 7;
        /// @custom:ensures result == old(v) + x
        /// @custom:ensures v == old(v) + x
        /// @custom:ensures w == (old(w) ^ x)
        /// @custom:succeeds-if v + x < 256
        function add(uint8 x) external returns (uint8) { v += x; w ^= x; return v; } }

`solar-verify --emit-lean` writes those specs as `Export.C4.Main`, whose meaning is
`SolidCore.Spec.Holds`: every call of `add` with a clean `uint8` argument finishes; when it succeeds
it returns a clean `uint8` equal to the old `v` plus `x`, `v` (the low byte of slot 0) is the old `v`
plus `x`, and `w` (the next byte) is the old `w` xor `x`; and when the old `v` plus `x` is below 256
it succeeds.

All of it is proved in Lean, with no trusted base: solar-verify's verdict, the one trusted item
of `spec_of_verdict`, is not used, since SolidCore's run of `add` is known exactly
(`Verify.C4.postAt`, by symbolic evaluation of SolidCore's interpreter from any storage that
writes slot 0). `post_of_postAt` reads that run through the spec's meaning.

* `holds_source`: the spec of SolidCore's checked `Main`, from any storage that writes slot 0.
* `holds_bytecode`: the spec of solar's runtime bytecode on EthLib, from the deployed storage,
  through the corpus's refinement (`Corpus.C4.refines_full`, solar 9688f215).
* `holds_bytecode_at`: from any storage that writes slot 0, given the stage from SolidCore to
  the bytecode that solar-tv's c4 milestone certifies (`Solar.C4.certified_at`, whose
  milestone proofs are outside this module's imports).
* `certified`: `holds_bytecode` bound to the export's manifest.
* `wrong_fails`: the negative test. With `result == old(v) + x + 1`
  (`scripts/refinement/spec/c4_wrong.sol`, which solar-verify also rejects) the spec does not hold
  of the bytecode, by a real mismatch: `add(0)` from the deployed storage returns 0.
-/

namespace SolidCore.Spec.Solar.C4

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Spec

/-- The call context of SolidCore's and EthLib's interface (`Refinement.Statement`): sender
`0x2000`, the contract at `0x1000`, block timestamp 1. -/
def ctxOf (call : Call) : Ctx :=
  { sender := 0x2000, value := call.callvalue, timestamp := 1, self := 0x1000 }

/-- c4 has no ghost state. -/
def step : GhostStep := fun _ g => g

theorem bytesWord_map (l : List UInt8) :
    bytesWord (l.map (·.toNat)) = EthLib.Base.bytesToNat l := by
  simp [bytesWord, EthLib.Base.bytesToNat, List.foldl_map]

theorem bytesWord_word {v : Nat} (h : v < 2 ^ 256) : bytesWord (Verify.word v) = v := by
  rw [Verify.word, bytesWord_map, EthLib.Base.bytesToNat_natToBytes_of_lt]
  simpa using h

theorem length_word (v : Nat) : (Verify.word v).length = 32 := by
  simp [Verify.word, EthLib.Base.natToBytes_length]

theorem words_word {v : Nat} (h : v < 2 ^ 256) : words (Verify.word v) = [v] := by
  simp only [words, length_word, Nat.reduceDiv, List.range_one, List.map_cons, List.map_nil,
    Nat.mul_zero, List.drop_zero]
  rw [List.take_of_length_le (by rw [length_word]), bytesWord_word h]

/-- The argument bytes of one word are the word's bytes. -/
theorem argBytes_one (a : Nat) : Dirty.argBytes [a] = Verify.word a := by
  simp [Dirty.argBytes, Verify.word]

/-- A call of the scope is `add` on one word `a` from a storage `σ`. -/
theorem scopeAt_call {call : Call} (h : Verify.C4.scopeAt call) :
    ∃ σ a, a < 2 ^ 256 ∧ call = Call.mk (Abi.calldata Bytecode.C4.Main.addSelector [a]) 0 σ := by
  obtain ⟨σ, _, fn, hfn, args, hlen, hargs, rfl⟩ := h
  simp only [Corpus.C4.fns, List.mem_singleton] at hfn
  subst hfn
  rcases args with _ | ⟨a, _ | _⟩ <;> simp at hlen
  exact ⟨σ, a, hargs a (by simp), rfl⟩

/-- The argument words after the selector of such a call. -/
theorem words_args (a : Nat) (ha : a < 2 ^ 256) :
    words (((Abi.calldata Bytecode.C4.Main.addSelector [a]).data.toList.map (·.toNat)).drop 4) =
      [a] := by
  rw [Dirty.bytes_calldata, Wide.drop_selector, argBytes_one, words_word ha]

/-- **SolidCore's run of `add`, read through the spec.** A call of the scope from a pre-state
meeting `Pre` that finishes as `Verify.C4.postAt` says finishes meeting `Post`. -/
theorem post_of_postAt {call : Call} (hs : Verify.C4.scopeAt call) {fs : FnSpec}
    (hfs : fs ∈ Export.C4.Main.spec.specs) {args : List Int} {pre : State}
    (hpre : Pre Export.C4.Main fs (ctxOf call) pre call args) {obs : Observable}
    (hpost : Verify.C4.postAt call obs) :
    Post Export.C4.Main fs (ctxOf call) pre (step call pre.ghost) obs args := by
  simp only [Export.C4.Main, List.mem_singleton] at hfs
  subst hfs
  obtain ⟨σ, a, ha, rfl⟩ := scopeAt_call hs
  obtain ⟨⟨_, _, hdec⟩, hst, -, -, -⟩ := hpre
  rw [words_args a ha] at hdec
  simp only [decodeWords, Ty.ofWord, Nat.reducePow] at hdec
  by_cases hx : a < 256
  swap
  · simp [hx] at hdec
  have hargs : args = [(a : Int)] := by
    simp [hx, bind, pure] at hdec
    exact hdec.symm
  subst hargs
  replace hx : a < 2 ^ 8 := hx
  have haw : Verify.argWords 1 (Call.mk (Abi.calldata Bytecode.C4.Main.addSelector [a]) 0 σ) =
      [a] :=
    Verify.argWords_calldata _ [a] (by simpa using ha) 0 σ
  simp only [Verify.C4.postAt, haw, List.getD_cons_zero, hx, ite_true] at hpost
  obtain ⟨hpost, -⟩ := hpost
  have hs0lt : slotValue σ 0 < 2 ^ 256 := SolidCore.Refinement.Evm.Wide.slotValue_lt σ 0
  have hpre0 : pre.storage 0 = slotValue σ 0 := by rw [hst]
  generalize slotValue σ 0 = s0 at hpost hs0lt hpre0
  by_cases hfit : s0 % 2 ^ 8 + a < 2 ^ 8
  · simp only [hfit, ite_true] at hpost
    obtain ⟨hsucc, hout, hstore⟩ := hpost
    have h0 := hstore 0
    simp only [Nat.zero_mod, ite_true] at h0
    have hy : s0 / 2 ^ 8 % 2 ^ 8 ^^^ a < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) hx
    refine ⟨fun _ => ⟨[((s0 % 2 ^ 8 + a : Nat) : Int)], ?_, ?_, ?_⟩, fun _ _ => hsucc⟩
    · rw [hout, words_word (by omega)]
      simp [decodeWords, Ty.ofWord, show s0 % 256 + a < 256 by omega]
    · simp [Bundle.satAll, Bundle.sat, eval, slotOf, mkEnv, Env.cur, BinOp.apply,
        Ty.ofBits, toWord, hpre0, h0]
      have e1 : ((s0 : Int) / 256 % 256 %
          115792089237316195423570985008687907853269984665640564039457584007913129639936).toNat =
          s0 / 2 ^ 8 % 2 ^ 8 := by omega
      have e2 : ((a : Int) %
          115792089237316195423570985008687907853269984665640564039457584007913129639936).toNat =
          a := by omega
      simp only [e1, e2]
      generalize s0 / 2 ^ 8 % 2 ^ 8 ^^^ a = y at hy ⊢
      constructor <;> omega
    · simp [Bundle.satAll, Export.C4.Main]
  · simp only [hfit, ite_false] at hpost
    refine ⟨fun h => by simp [hpost.1] at h, fun _ hsi => ?_⟩
    simp [Bundle.satAll, Bundle.sat, eval, slotOf, mkEnv, Env.cur, BinOp.apply,
      Ty.ofBits, toWord, hpre0] at hsi
    omega

/-! ## The spec of SolidCore and of the bytecode -/

/-- **The spec of SolidCore's checked `Main`**, on every call of `add` from any storage that writes
slot 0. -/
theorem holds_source : ∃ c, Corpus.C4.contract? = .ok c ∧
    Holds (solidCore Corpus.C4.fuel) c Verify.C4.scopeAt Export.C4.Main ctxOf step := by
  obtain ⟨c, hc, hsat⟩ := Verify.C4.satisfiesAt
  refine ⟨c, hc, fun fs hfs call hs args pre hpre => ?_⟩
  obtain ⟨obs, hrun, hpost⟩ := hsat call hs trivial
  exact ⟨obs, hrun, post_of_postAt hs hfs hpre hpost⟩

/-- SolidCore's run of `add` from any storage, carried to the bytecode on the deployed storage by
the corpus refinement. -/
theorem satisfies_bytecode :
    Satisfies ethLib Corpus.C4.code Verify.C4.scope Verify.C4.pre Verify.C4.postAt := by
  obtain ⟨c, hc, hsat⟩ := Verify.C4.satisfiesAt
  obtain ⟨c', s, hc', hs', href⟩ := Corpus.C4.refines_full
  rw [hc] at hc'
  cases hc'
  have hs : s = Verify.C4.deployed := by
    rw [(Verify.C4.shape_of hc).2.1] at hs'
    exact (Option.some.inj hs').symm
  subst hs
  exact bytecode_of_refines (fun call h hp => hsat call (Verify.C4.scopeAt_of_scope h) hp) href

/-- **The spec of solar's runtime bytecode on EthLib**, on every call of `add` (any argument word,
no value) from the deployed storage. -/
theorem holds_bytecode :
    Holds ethLib Corpus.C4.code Verify.C4.scope Export.C4.Main ctxOf step := by
  intro fs hfs call hs args pre hpre
  obtain ⟨obs, hrun, hpost⟩ := satisfies_bytecode call hs trivial
  exact ⟨obs, hrun, post_of_postAt (Verify.C4.scopeAt_of_scope hs) hfs hpre hpost⟩

/-- **The spec of the bytecode from any storage that writes slot 0**, given the stage from
SolidCore to the bytecode on that scope, which solar-tv's c4 milestone certifies
(`SolidCore.Refinement.Solar.C4.certified_at`). -/
theorem holds_bytecode_at {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.C4.contract? = .ok c)
    (stage : Stage (solidCore Corpus.C4.fuel) ethLib c Corpus.C4.code Verify.C4.scopeAt) :
    Holds ethLib Corpus.C4.code Verify.C4.scopeAt Export.C4.Main ctxOf step := by
  obtain ⟨c', hc', h⟩ := holds_source
  rw [hc] at hc'
  cases hc'
  exact h.of_stage stage

/-- **c4's solar-verify spec, certified on solar's bytecode**, bound to the export's manifest:
the annotated source's sha256, the compiler that built the bytecode, the bytecode's sha256 (that
of `Bytecode.C4.Main.runtimeNat`'s 107 bytes, which `scripts/refinement/spec/check.sh` checks
outside the kernel, as solar's certify.sh does), the spec's well-formedness, and the spec. -/
theorem certified :
    Export.C4.manifest.sourceSha256 =
      "f6a3a1d0280a07e6f5697b57489f426936b41078de11390f18fe62a313a495c9" ∧
    Export.C4.manifest.compiler = "solar 0.3.0-dev+commit.9688f215" ∧
    Bytecode.C4.solarRev = "9688f21581717743806cb7bf3afae2ac3c156a08" ∧
    Export.C4.manifest.bytecodeSha256 =
      "8a21bc207d9dd8be48d921a717eda3ecb7e5bfcb5397850bc3d64a29037fac47" ∧
    Export.C4.Main.WF = true ∧
    Holds ethLib Corpus.C4.code Verify.C4.scope Export.C4.Main ctxOf step :=
  ⟨rfl, rfl, rfl, rfl, Export.C4.Main_wf, holds_bytecode⟩

/-! ## The negative test -/

/-- The call `add(0)` from the deployed storage. -/
def call0 : Call := Call.mk (Abi.calldata Bytecode.C4.Main.addSelector [0]) 0 Verify.C4.deployed

theorem selectorOf_calldata (sel : Nat) (hsel : sel < 2 ^ 32) (args : List Nat) :
    selectorOf (Call.mk (Abi.calldata sel args) 0 []) = sel := by
  simp only [selectorOf, Dirty.bytes_calldata]
  rw [List.take_append_of_le_length (by simp [EthLib.Base.natToBytes_length]),
    List.take_of_length_le (by simp [EthLib.Base.natToBytes_length]), bytesWord_map,
    EthLib.Base.bytesToNat_natToBytes_of_lt (by simpa using hsel)]

/-- **The wrong spec fails, by a mismatch.** `result == old(v) + x + 1` does not hold of the
bytecode: `add(0)` from the deployed storage returns 0, and the spec asks for 1. -/
theorem wrong_fails :
    ¬ Holds ethLib Corpus.C4.code Verify.C4.scope Export.C4Wrong.Main ctxOf step := by
  intro h
  have hs : Verify.C4.scope call0 :=
    ⟨_, List.mem_singleton_self _, [0], rfl, by simp, rfl⟩
  let pre : State := ⟨slotValue call0.storage, Ghost.zero, 0⟩
  have hfs := List.mem_singleton_self (Export.C4Wrong.Main.spec.specs.head (by simp [Export.C4Wrong.Main]))
  have hdec : decodeWords [.uint 8]
      (words ((call0.calldata.data.toList.map (·.toNat)).drop 4)) = some [0] := by
    rw [call0, words_args 0 (by decide)]
    simp [decodeWords, Ty.ofWord, bind, pure]
  have hpre : Pre Export.C4Wrong.Main (Export.C4Wrong.Main.spec.specs.head (by simp [Export.C4Wrong.Main]))
      (ctxOf call0) pre call0 [0] := by
    refine ⟨⟨?_, ?_, ?_⟩, rfl, by simp [pre, ctxOf], ?_, ?_⟩
    · simp [call0, Abi.calldata, EthLib.Base.natToBytes_length, ByteArray.size]
    · show selectorOf call0 = Bytecode.C4.Main.addSelector
      have := selectorOf_calldata Bytecode.C4.Main.addSelector (by decide) [0]
      exact this
    · simpa [Export.C4Wrong.Main] using hdec
    · simp [Bundle.satAll, Export.C4Wrong.Main]
    · simp [Bundle.satAll, Export.C4Wrong.Main]
  obtain ⟨obs, hrun, hpost⟩ := h _ (by simpa [Export.C4Wrong.Main] using hfs) call0 hs [0] pre hpre
  obtain ⟨obs', hrun', hpost'⟩ := satisfies_bytecode call0 hs trivial
  rw [hrun] at hrun'
  cases hrun'
  have haw : Verify.argWords 1 call0 = [0] :=
    Verify.argWords_calldata _ [0] (by simp) 0 Verify.C4.deployed
  simp only [Verify.C4.postAt, haw] at hpost'
  simp [call0, Verify.C4.deployed, slotValue] at hpost'
  obtain ⟨⟨hsucc, hout, -⟩, -⟩ := hpost'
  obtain ⟨rets, hrets, hens, -⟩ := hpost.1 hsucc
  rw [hout, words_word (by decide)] at hrets
  simp [decodeWords, Ty.ofWord, bind, pure, Export.C4Wrong.Main, List.head] at hrets
  subst hrets
  have := hens _ (by simp [Export.C4Wrong.Main, List.head]; exact Or.inl rfl)
  simp [Bundle.sat, Export.C4Wrong.Main, eval, slotOf, mkEnv, Env.cur, BinOp.apply, Ty.ofBits,
    toWord, pre, call0, Verify.C4.deployed, slotValue] at this

end SolidCore.Spec.Solar.C4
