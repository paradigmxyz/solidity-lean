import EthLib.Execution.Proofs.Evm.Call.StepRules
import EthLib.Execution.Proofs.Evm.Logic.Message

/-!
# EthLib's runner of messages gives an output that a word can size

A frame sets its output only at its start (empty), at an exceptional halt (empty), at RETURN
and REVERT (a range of memory whose size is a word), in a precompile and at the deposit of code
(empty, or kept). Every precompile gives a fixed number of bytes, the call data (IDENTITY), or as
many bytes as the length of the modulus that the call data names in one word (MODEXP).

* OStep: a step that keeps the message, and keeps an output that a word can size so.
* oResult_step: every step is one, and so is the caller that resumes after a message.
* fits_process: a message whose data a word can size ends with an output that a word can size,
  however deep its calls: the induction on the gas of messages
  (EthLib.Execution.Evm.processMessage_rel).
* meets_outputFitsIn: the interpreter's runner of messages meets that.
-/

namespace EthLib.Execution.Evm.OutputBound

open EthLib
open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.Evm
open EthLib.Execution.State (TransactionState)

/-! ## Precompiles -/

section Precompiles

open EthLib.Execution.Evm.Precompiles

theorem size_ecrecover_output (hash : Vector UInt8 32) (v r s : Nat) :
    (Ecrecover.output hash v r s).size < 2 ^ 256 := by
  unfold Ecrecover.output
  split
  · split
    · simp [ByteArray.size]
    · simp
  · simp

theorem size_ecrecover {data out : ByteArray} {gas : Nat}
    (h : Ecrecover.ecrecover data gas = .ok out) : out.size < 2 ^ 256 := by
  unfold Ecrecover.ecrecover at h
  split at h
  · cases h
  · rw [← Except.ok.inj h]
    exact size_ecrecover_output _ _ _ _

theorem size_sha256_hash (m : ByteArray) : (Cryptography.Hash.sha256 m).size = 32 := by
  simp only [Cryptography.Hash.sha256, Cryptography.Hash.Sha256.hash,
    Cryptography.Hash.Sha256.digest, ByteArray.size, List.size_toArray, List.length_cons,
    List.length_nil]

theorem size_sha256 {data out : ByteArray} {gas : Nat}
    (h : Sha256.sha256 data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Sha256.sha256] at h
  split at h
  · cases h
  · cases h
    rw [size_sha256_hash]
    decide

theorem size_ripemd160_hash (m : ByteArray) : (Cryptography.Hash.ripemd160 m).size = 20 := by
  simp only [Cryptography.Hash.ripemd160, Cryptography.Hash.Ripemd160.hash,
    Cryptography.Hash.Ripemd160.digest, ByteArray.size, Array.size_ofFn]

theorem size_ripemd160 {data out : ByteArray} {gas : Nat}
    (h : Ripemd160.ripemd160 data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Ripemd160.ripemd160] at h
  split at h
  · cases h
  · cases h
    unfold Ripemd160.output
    rw [ByteArray.size_append, size_ripemd160_hash]
    simp [ByteArray.size, Ripemd160.OUTPUT_BYTES, Ripemd160.DIGEST_BYTES]

theorem size_identity {data out : ByteArray} {gas : Nat}
    (h : Identity.identity data gas = .ok out) (hd : data.size < 2 ^ 256) :
    out.size < 2 ^ 256 := by
  simp only [Identity.identity] at h
  split at h
  · cases h
  · cases h
    exact hd

theorem size_modexp {fork : Fork} {data out : ByteArray} {gas : Nat}
    (h : Modexp.modexp fork data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Modexp.modexp] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      have hl := Base.bytesToNat_lt
        (bufferRead data (2 * Modexp.LENGTH_HEADER_BYTES) Modexp.LENGTH_HEADER_BYTES)
      rw [bufferRead_length] at hl
      simpa [Modexp.compute, ByteArray.size, Base.natToBytes_length, Modexp.parseLengths,
        Modexp.readNat, Modexp.LENGTH_HEADER_BYTES] using hl

theorem length_altBn128_g1ToBytes (point : Cryptography.AltBn128.Point) :
    (AltBn128.g1ToBytes point).length = 64 := by
  cases point <;> simp [AltBn128.g1ToBytes, Base.natToBytes_length]

theorem size_ecadd {fork : Fork} {data out : ByteArray} {gas : Nat}
    (h : AltBn128.ecadd fork data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [AltBn128.ecadd, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
  cases h
  simp [ByteArray.size, length_altBn128_g1ToBytes]

theorem size_ecmul {fork : Fork} {data out : ByteArray} {gas : Nat}
    (h : AltBn128.ecmul fork data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [AltBn128.ecmul, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
  cases h
  simp [ByteArray.size, length_altBn128_g1ToBytes]

theorem size_ecpairing {fork : Fork} {data out : ByteArray} {gas : Nat}
    (h : AltBn128.ecpairing fork data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [AltBn128.ecpairing, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
  cases h
  simp [ByteArray.size, AltBn128.ecpairingWord]

theorem size_blake2f {data out : ByteArray} {gas : Nat}
    (h : Blake2f.blake2f data gas = .ok out) : out.size < 2 ^ 256 := by
  unfold Blake2f.blake2f at h
  split at h
  · cases h
  split at h
  · cases h
  cases ho : Blake2f.output data with
  | error e => simp [ho, Except.map] at h
  | ok v =>
    simp only [ho, Except.map, Except.ok.injEq] at h
    subst h
    simp [ByteArray.size, Blake2f.OUTPUT_BYTES]

theorem size_pointEvaluation {data out : ByteArray} {gas : Nat}
    (h : PointEvaluation.pointEvaluation data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [PointEvaluation.pointEvaluation, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure] at h
  repeat' (first | (split at h) | (cases h; done))
  all_goals first
    | (cases h; done)
    | (cases h; simp [PointEvaluation.output, ByteArray.size, Base.natToBytes_length])

theorem length_padG1_g1ToBytes (point : Cryptography.Bls.G1) :
    (Bls12381.padG1 (Bls12381.g1ToBytes point)).length = 128 := by
  simp [Bls12381.padG1, Bls12381.g1ToBytes, Bls12381.zeroPad, Bls12381.PAD_BYTES,
    Base.natToBytes_length]

theorem length_padG2_g2ToBytes (point : Cryptography.Bls.G2) :
    (Bls12381.padG2 (Bls12381.g2ToBytes point)).length = 256 := by
  simp [Bls12381.padG2, Bls12381.g2ToBytes, Bls12381.zeroPad, Bls12381.PAD_BYTES,
    Base.natToBytes_length]

set_option hygiene false in
/-- Closes the bound on the output of a BLS12-381 precompile from `h`. -/
local macro "bls_size" : tactic => `(tactic| (
  split at h
  · cases h
  split at h
  · cases h
  repeat obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
  cases h
  simp [ByteArray.size, length_padG1_g1ToBytes, length_padG2_g2ToBytes,
    Bls12381.boolWord]))

theorem size_bls12G1Add {data out : ByteArray} {gas : Nat}
    (h : Bls12381.bls12G1Add data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Bls12381.bls12G1Add, bind, throw, throwThe, MonadExceptOf.throw] at h
  bls_size

theorem size_bls12G1Msm {data out : ByteArray} {gas : Nat}
    (h : Bls12381.bls12G1Msm data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Bls12381.bls12G1Msm, bind, throw, throwThe, MonadExceptOf.throw] at h
  bls_size

theorem size_bls12G2Add {data out : ByteArray} {gas : Nat}
    (h : Bls12381.bls12G2Add data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Bls12381.bls12G2Add, bind, throw, throwThe, MonadExceptOf.throw] at h
  bls_size

theorem size_bls12G2Msm {data out : ByteArray} {gas : Nat}
    (h : Bls12381.bls12G2Msm data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Bls12381.bls12G2Msm, bind, throw, throwThe, MonadExceptOf.throw] at h
  bls_size

theorem size_bls12Pairing {data out : ByteArray} {gas : Nat}
    (h : Bls12381.bls12Pairing data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Bls12381.bls12Pairing, bind, throw, throwThe, MonadExceptOf.throw] at h
  bls_size

theorem size_bls12MapFpToG1 {data out : ByteArray} {gas : Nat}
    (h : Bls12381.bls12MapFpToG1 data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Bls12381.bls12MapFpToG1, bind, throw, throwThe, MonadExceptOf.throw] at h
  bls_size

theorem size_bls12MapFp2ToG2 {data out : ByteArray} {gas : Nat}
    (h : Bls12381.bls12MapFp2ToG2 data gas = .ok out) : out.size < 2 ^ 256 := by
  simp only [Bls12381.bls12MapFp2ToG2, bind, throw, throwThe, MonadExceptOf.throw] at h
  bls_size

theorem size_p256Verify {data out : ByteArray} {gas : Nat}
    (h : P256Verify.p256Verify data gas = .ok out) : out.size < 2 ^ 256 := by
  unfold P256Verify.p256Verify at h
  split at h
  · cases h
  split at h
  · cases h; simp
  split at h
  · cases h; simp [P256Verify.VALID, ByteArray.size]
  · cases h; simp

/-- **Every precompile gives an output that a word can size**, from call data that a word can
size. -/
theorem size_run_lt {fork : Fork} {address : Nat} {data out : ByteArray} {gas : Nat}
    (h : Precompiles.run fork address data gas = some (.ok out)) (hd : data.size < 2 ^ 256) :
    out.size < 2 ^ 256 := by
  unfold Precompiles.run at h
  split at h
  · cases h
  split at h
  all_goals first
    | cases h
    | skip
  all_goals
    have h := Base.mapError_ok_iff.mp (Option.some.inj h)
  all_goals first
    | exact size_ecrecover h
    | exact size_sha256 h
    | exact size_ripemd160 h
    | exact size_identity h hd
    | exact size_modexp h
    | exact size_ecadd h
    | exact size_ecmul h
    | exact size_ecpairing h
    | exact size_blake2f h
    | exact size_pointEvaluation h
    | exact size_bls12G1Add h
    | exact size_bls12G1Msm h
    | exact size_bls12G2Add h
    | exact size_bls12G2Msm h
    | exact size_bls12Pairing h
    | exact size_bls12MapFpToG1 h
    | exact size_bls12MapFp2ToG2 h
    | exact size_p256Verify h

end Precompiles


/-! ## Steps that keep the message and an output that a word can size -/

variable {fork : Fork} {Meter : Type}

/-- A step that keeps the message, and keeps an output that a word can size so. -/
structure OStep (before after : Evm fork Meter) : Prop where
  message : after.message = before.message
  output : before.output.size < 2 ^ 256 → after.output.size < 2 ^ 256

namespace OStep

theorem refl (evm : Evm fork Meter) : OStep evm evm := ⟨rfl, id⟩

theorem trans {a b c : Evm fork Meter} (hab : OStep a b) (hbc : OStep b c) : OStep a c :=
  ⟨hbc.message.trans hab.message, fun h => hbc.output (hab.output h)⟩

theorem withMemory (evm : Evm fork Meter) (memory : ByteArray) : OStep evm { evm with memory } :=
  ⟨rfl, id⟩

theorem advance {a b : Evm fork Meter} (h : OStep a b) (n : Nat := 1) :
    OStep a (Evm.advance b n) :=
  ⟨h.message, h.output⟩

end OStep

theorem oStep_popWord {evm after : Evm fork Meter} {x : U256}
    (h : popWord evm = .ok (x, after)) : OStep evm after := by
  obtain ⟨⟨_, _⟩, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨rfl, id⟩

theorem oStep_pushWord {evm after : Evm fork Meter} {x : U256}
    (h : pushWord evm x = .ok after) : OStep evm after := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨rfl, id⟩

theorem oStep_recordAccountRead (evm : Evm fork Meter) (address : Address) :
    OStep evm (recordAccountRead evm address) := ⟨rfl, id⟩

theorem oStep_recordStorageRead (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    OStep evm (recordStorageRead evm address key) := ⟨rfl, id⟩

theorem oStep_accessAddress (evm : Evm fork Meter) (address : Address) :
    OStep evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  rw [h]
  exact ⟨rfl, id⟩

theorem oStep_accessStorageKey (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    OStep evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  rw [h]
  exact ⟨rfl, id⟩

theorem oStep_popTopics {evm after : Evm fork Meter} {n : Nat} {topics : List Base.Hash32}
    (h : popTopics evm n = .ok (topics, after)) : OStep evm after := by
  induction n generalizing evm topics with
  | zero =>
    cases h
    exact OStep.refl _
  | succ k ih =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨ts, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (oStep_popWord h1).trans (ih h2)

/-- The pops of the operands of a call keep the message and the output. -/
theorem oStep_popCallOperands {kind : CallKind} {evm after : Evm fork Meter}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    OStep evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨v, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have p3 : OStep e2 e3 := by
    unfold popCallValue at h3
    split at h3
    · exact oStep_popWord h3
    · cases h3
      exact OStep.refl _
  exact ((((((oStep_popWord h1).trans (oStep_popWord h2)).trans p3).trans
    (oStep_popWord h4)).trans (oStep_popWord h5)).trans (oStep_popWord h6)).trans
    (oStep_popWord h7)

variable [GasMeter Meter]

theorem oStep_chargeGas {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeGas evm amount = .ok after) : OStep evm after := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨rfl, id⟩

theorem oStep_chargeStateGas {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeStateGas evm amount = .ok after) : OStep evm after := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨rfl, id⟩

theorem oStep_chargeGasAndMemory {evm after : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} (h : chargeGasAndMemory evm cost ranges = .ok after) :
    OStep evm after := by
  obtain ⟨_, hc, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have := oStep_chargeGas hc
  exact ⟨this.message, this.output⟩

theorem oStep_refillStateGas (evm : Evm fork Meter) (amount : Nat) :
    OStep evm (refillStateGas evm amount) := ⟨rfl, id⟩

theorem oStep_readFrame {cost : Nat} {value : Evm fork Meter → U256}
    {evm after : Evm fork Meter} (h : readFrame cost value evm = .ok after) :
    OStep evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((oStep_chargeGas h1).trans (oStep_pushWord h2)).advance

theorem oStep_unaryOp {cost : Nat} {f : U256 → U256} {evm after : Evm fork Meter}
    (h : unaryOp cost f evm = .ok after) : OStep evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((oStep_popWord h1).trans (oStep_chargeGas h2)).trans (oStep_pushWord h3)).advance

theorem oStep_binaryOp {cost : Nat} {f : U256 → U256 → U256} {evm after : Evm fork Meter}
    (h : binaryOp cost f evm = .ok after) : OStep evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((oStep_popWord h1).trans (oStep_popWord h2)).trans (oStep_chargeGas h3)).trans
    (oStep_pushWord h4)).advance

theorem oStep_ternaryOp {cost : Nat} {f : U256 → U256 → U256 → U256}
    {evm after : Evm fork Meter} (h : ternaryOp cost f evm = .ok after) : OStep evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((((oStep_popWord h1).trans (oStep_popWord h2)).trans (oStep_popWord h3)).trans
    (oStep_chargeGas h4)).trans (oStep_pushWord h5)).advance

/-- An exceptional halt drops the output. -/
theorem oStep_exceptionalHalt (evm : Evm fork Meter) (e : EvmError) :
    OStep evm (exceptionalHalt evm e) :=
  ⟨rfl, fun _ => by simp [exceptionalHalt]⟩

/-! ## The instructions that give the next frame -/

theorem oStep_dupnStep {evm after : Evm fork Meter} (h : dupnStep evm = .ok after) :
    OStep evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
    · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact ((oStep_chargeGas h1).trans (oStep_pushWord h2)).advance _
  · cases h

theorem oStep_swapnStep {evm after : Evm fork Meter} (h : swapnStep evm = .ok after) :
    OStep evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      have := oStep_chargeGas h1
      exact ⟨this.message, this.output⟩
    · cases h
  · cases h

theorem oStep_exchangeStep {evm after : Evm fork Meter} (h : exchangeStep evm = .ok after) :
    OStep evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      have := oStep_chargeGas h1
      exact ⟨this.message, this.output⟩
    · cases h
  · cases h

theorem oStep_stackOnlyStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | exact oStep_dupnStep h
    | exact oStep_swapnStep h
    | exact oStep_exchangeStep h
    | exact oStep_unaryOp h
    | exact oStep_binaryOp h
    | exact oStep_ternaryOp h
    | skip
  case exp | keccak256 =>
    simp only [expStep, keccak256Step] at h
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    first
      | exact ((((oStep_popWord h1).trans (oStep_popWord h2)).trans
          (oStep_chargeGas h3)).trans (oStep_pushWord h4)).advance
      | exact ((((oStep_popWord h1).trans (oStep_popWord h2)).trans
          (oStep_chargeGasAndMemory h3)).trans (oStep_pushWord h4)).advance
  case pop =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((oStep_popWord h1).trans (oStep_chargeGas h2)).advance
  case push =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((oStep_chargeGas h1).trans (oStep_pushWord h2)).advance _
  case dup =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h
    · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact ((oStep_chargeGas h1).trans (oStep_pushWord h2)).advance
  case swap =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · split at h
      · cases h
      · cases h
        have := oStep_chargeGas h1
        exact ⟨this.message, this.output⟩
    · cases h

theorem oStep_controlFlowStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : controlFlowStep op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  case pc | gas => exact oStep_readFrame h
  case stop =>
    cases h
    exact ⟨rfl, id⟩
  case jumpdest =>
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (oStep_chargeGas h1).advance
  case jump =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · cases h
      have := (oStep_popWord h1).trans (oStep_chargeGas h2)
      exact ⟨this.message, this.output⟩
    · cases h
  case jumpi =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    have := ((oStep_popWord h1).trans (oStep_popWord h2)).trans (oStep_chargeGas h3)
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · cases h
      exact this.advance
    · split at h
      · cases h
        exact ⟨this.message, this.output⟩
      · cases h

theorem oStep_memoryDataStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  case msize | calldatasize | codesize | returndatasize => exact oStep_readFrame h
  case mload =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (((oStep_popWord h1).trans (oStep_chargeGasAndMemory h2)).trans
      (oStep_pushWord h3)).advance
  case mstore | mstore8 =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have := ((oStep_popWord h1).trans (oStep_popWord h2)).trans (oStep_chargeGasAndMemory h3)
    exact ⟨this.message, this.output⟩
  case calldataload =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (((oStep_popWord h1).trans (oStep_chargeGas h2)).trans (oStep_pushWord h3)).advance
  case mcopy | calldatacopy | codecopy =>
    first
      | simp only [mcopyStep] at h
      | simp only [copyToMemory] at h
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have := (((oStep_popWord h1).trans (oStep_popWord h2)).trans
      (oStep_popWord h3)).trans (oStep_chargeGasAndMemory h4)
    exact ⟨this.message, this.output⟩
  case returndatacopy =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · cases h
    · cases h
      have := (((oStep_popWord h1).trans (oStep_popWord h2)).trans
        (oStep_popWord h3)).trans (oStep_chargeGas h4)
      exact ⟨this.message, this.output⟩

/-- The output of RETURN and REVERT is a range of memory whose size is a word. -/
theorem oStep_haltWithOutput {evm after : Evm fork Meter} (h : haltWithOutput evm = .ok after) :
    OStep evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨size, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have c := ((oStep_popWord h1).trans (oStep_popWord h2)).trans (oStep_chargeGasAndMemory h3)
  refine ⟨c.message, fun _ => Nat.lt_of_le_of_lt ?_ size.isLt⟩
  show (memoryReadBytes _ _ _).size ≤ _
  unfold memoryReadBytes
  split
  · simp
  · simp only [ByteArray.size_extract]
    omega

theorem oStep_returnOpStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  case «return» => subst hstep; exact oStep_haltWithOutput h
  case revert =>
    split at hstep
    · cases hstep
      obtain ⟨e, he, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have := oStep_haltWithOutput he
      exact ⟨this.message, this.output⟩
    · cases hstep

theorem oStep_environmentStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals first
    | (subst hstep; exact oStep_readFrame h)
    | skip
  case prevrandao =>
    split at hstep <;> (simp only [Option.some.injEq] at hstep; subst hstep) <;>
      exact oStep_readFrame h
  case chainid | basefee | blobbasefee | slotnum =>
    split at hstep
    · simp only [Option.some.injEq] at hstep
      subst hstep
      exact oStep_readFrame h
    · cases hstep
  case blobhash =>
    split at hstep
    · simp only [Option.some.injEq] at hstep
      subst hstep
      obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (((oStep_popWord h1).trans (oStep_chargeGas h2)).trans (oStep_pushWord h3)).advance
    · cases hstep
  case blockhash =>
    subst hstep
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (((oStep_popWord h1).trans (oStep_chargeGas h2)).trans (oStep_pushWord h3)).advance

set_option hygiene false in
/-- Closes `OStep evm after` from `h : step evm = .ok after` for a step that pops an address,
accesses it, charges, may read its code, records the read and pushes one word. -/
local macro "ostep_read" : tactic => `(tactic| (
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : OStep e1 e2 := by
    have := oStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  try obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((oStep_popWord h1).trans ha).trans (oStep_chargeGas h3)).trans
    (oStep_recordAccountRead _ _)).trans (oStep_pushWord h4) |>.advance))

theorem oStep_balanceStep {evm after : Evm fork Meter} (h : balanceStep evm = .ok after) :
    OStep evm after := by
  ostep_read

theorem oStep_extcodesizeStep {evm after : Evm fork Meter}
    (h : extcodesizeStep evm = .ok after) : OStep evm after := by
  ostep_read

theorem oStep_extcodehashStep {evm after : Evm fork Meter}
    (h : extcodehashStep evm = .ok after) : OStep evm after := by
  ostep_read

theorem oStep_extcodecopyStep {evm after : Evm fork Meter}
    (h : extcodecopyStep evm = .ok after) : OStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨st, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨off, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨sz, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e4 (toAddressMasked w) with ⟨cold, e5⟩
  simp only [hacc] at h
  obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : OStep e4 e5 := by
    have := oStep_accessAddress e4 (toAddressMasked w)
    rwa [hacc] at this
  exact (((((((oStep_popWord h1).trans (oStep_popWord h2)).trans (oStep_popWord h3)).trans
    (oStep_popWord h4)).trans ha).trans (oStep_chargeGasAndMemory h6)).trans
    (oStep_recordAccountRead _ _)).trans (OStep.withMemory _ _) |>.advance

theorem oStep_accountStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance => subst hstep; exact oStep_balanceStep h
  case extcodesize => subst hstep; exact oStep_extcodesizeStep h
  case extcodecopy => subst hstep; exact oStep_extcodecopyStep h
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (oStep_recordAccountRead _ _).trans (oStep_readFrame h)
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep; exact oStep_extcodehashStep h
    · cases hstep

theorem oStep_sloadStep {evm after : Evm fork Meter} (h : sloadStep evm = .ok after) :
    OStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : OStep e1 e2 := by
    have := oStep_accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w)
    rwa [hacc] at this
  exact ((((oStep_popWord h1).trans ha).trans (oStep_chargeGas h3)).trans
    (oStep_recordStorageRead _ _ _)).trans (oStep_pushWord h4) |>.advance

theorem oStep_sstoreStep {evm after : Evm fork Meter} (h : sstoreStep evm = .ok after) :
    OStep evm after := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 := (oStep_popWord h1).trans (oStep_popWord h2)
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    have ha : OStep evm (recordStorageRead e3 e2.message.currentTarget (U256.toBeBytes k)) := by
      have := oStep_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
      rw [hpair] at this
      exact (c2.trans this).trans (oStep_recordStorageRead _ _ _)
    simp only [hpair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : OStep evm e5 :=
        ha.trans ((oStep_refillStateGas _ _).trans
          ((oStep_chargeGas h4).trans (oStep_chargeStateGas h5)))
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, -, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact ⟨m5.message, m5.output⟩
    · exact ha.trans (oStep_exceptionalHalt _ _)

theorem oStep_storageStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep
  case sload => subst hstep; exact oStep_sloadStep h
  case sstore => subst hstep; exact oStep_sstoreStep h

theorem oStep_tloadStep {evm after : Evm fork Meter} (h : tloadStep evm = .ok after) :
    OStep evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((oStep_popWord h1).trans (oStep_chargeGas h2)).trans (oStep_pushWord h3)).advance

theorem oStep_tstoreStep {evm after : Evm fork Meter} (h : tstoreStep evm = .ok after) :
    OStep evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    have c := (oStep_popWord h1).trans ((oStep_popWord h2).trans (oStep_chargeGas h3))
    exact ⟨c.message, c.output⟩

theorem oStep_transientStorageStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  case tload => exact oStep_tloadStep h
  case tstore => exact oStep_tstoreStep h

theorem oStep_logStep {n : Nat} {evm after : Evm fork Meter} (h : logStep n evm = .ok after) :
    OStep evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  have c := (((oStep_popWord h1).trans (oStep_popWord h2)).trans (oStep_popTopics h3)).trans
    (oStep_chargeGasAndMemory h4)
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact ⟨c.message, c.output⟩

theorem oStep_logOpStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact oStep_logStep h

omit [GasMeter Meter] in
theorem oStep_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    OStep evm after := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ⟨rfl, id⟩

theorem oStep_selfdestructStep {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) : OStep evm after := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : OStep e1 e2 := by
    have := oStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c := ((oStep_popWord h1).trans ha).trans (oStep_recordAccountRead e2 (toAddressMasked w))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    exact ((c.trans (oStep_chargeGas h3)).trans (oStep_chargeStateGas h4)).trans
      (oStep_finishSelfdestruct h)
  · exact c.trans (oStep_exceptionalHalt _ _)

theorem oStep_selfdestructOpStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : OStep evm after := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact oStep_selfdestructStep h

/-- **Each instruction that gives the next frame keeps the message, and an output that a word
can size.** -/
theorem oStep_instruction {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) : OStep evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact oStep_stackOnlyStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact oStep_controlFlowStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact oStep_memoryDataStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact oStep_returnOpStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact oStep_environmentStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact oStep_accountStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact oStep_storageStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact oStep_transientStorageStep hf h
  rcases orElse_eq_some hrun with hf | hf
  · exact oStep_logOpStep hf h
  · exact oStep_selfdestructOpStep hf h

/-! ## The steps that send a message -/

theorem oStep_accessDelegation {evm after : Evm fork Meter} {address : Address}
    {known : Nat} {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    OStep evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (oStep_accessAddress _ _).trans (oStep_recordAccountRead _ _)
  · cases h
    exact OStep.refl _

theorem oStep_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    OStep evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((oStep_chargeGas h1).trans (oStep_chargeStateGas h2)).trans (oStep_chargeGas h3)
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact oStep_chargeGas h1

theorem oStep_skipCall {evm after : Evm fork Meter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : OStep evm after := by
  obtain ⟨stack, -, rfl⟩ := skipCall_eq_ok h
  exact ⟨rfl, id⟩

/-- The caller that takes in a child keeps its output. -/
theorem output_incorporateChild (caller child : Evm fork Meter) :
    (incorporateChild fork caller child).output = caller.output := by
  unfold incorporateChild
  split <;> rfl

/-- What a step gives: a step that keeps the message and an output that a word can size, or a
message from such a step, after which the caller resumes with such a step, whatever the child. -/
def OResult (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after => OStep evm after
  | .child caller _ resume =>
    OStep evm caller ∧ ∀ child after, resume child = .ok after → OStep evm after

omit [GasMeter Meter] in
theorem OResult.lift {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (h : OStep evm evm') (r : OResult evm' result) : OResult evm result := by
  cases result with
  | next after => exact h.trans r
  | child caller message resume =>
    obtain ⟨c, k⟩ := r
    exact ⟨h.trans c, fun child after hres => h.trans (k child after hres)⟩

/-- A caller that resumes after a call keeps its message and its output. -/
theorem oStep_resumeCall {caller child after : Evm fork Meter} {newAccount : Nat}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    OStep caller after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hp := oStep_pushWord h1
  refine ⟨hp.message.trans ?_, fun hc => hp.output ?_⟩
  · split <;> simp [message_incorporateChild, refillStateGas]
  · split <;> simpa [output_incorporateChild, refillStateGas] using hc

/-- A creator that resumes after a creation keeps its message and its output. -/
theorem oStep_resumeCreate {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (h : resumeCreate fork caller newAccount address child = .ok after) :
    OStep caller after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hp := oStep_pushWord h1
  refine ⟨hp.message.trans ?_, fun hc => hp.output ?_⟩
  · split <;> simp [message_incorporateChild, refillStateGas]
  · split <;> simpa [output_incorporateChild, refillStateGas] using hc

theorem oResult_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    OResult evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · cases hs : skipCall (refillStateGas { evm with returnData := .empty } newAccount)
        message.gas message.reservoir with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      exact (⟨rfl, id⟩ : OStep evm
        (refillStateGas { evm with returnData := .empty } newAccount)).trans
        (oStep_skipCall hs)
  · cases h
    refine ⟨⟨rfl, id⟩, ?_⟩
    intro child after hres
    exact (⟨rfl, id⟩ : OStep evm { evm with returnData := .empty }).trans
      (oStep_resumeCall hres)

theorem oResult_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    OResult evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  have pre : OStep evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) := ⟨rfl, id⟩
  split at h
  · cases hs : skipCall (refillStateGas (recordAccountRead { evm with
        memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        evm.message.currentTarget) newAccount) subCall (GasMeter.reservoir evm.gas) with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      exact (pre.trans (oStep_refillStateGas _ _)).trans (oStep_skipCall hs)
  · exact OResult.lift pre (oResult_genericCall h)

theorem oResult_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    OResult evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 := oStep_popCallOperands h1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : OStep e1 e2 := by
    have := oStep_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : OStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (oStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : OStep evm e4 := s3.trans (oStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact OResult.lift (s4.trans (oStep_payCall h5)) (oResult_finishCall h)
    · exact s4.trans (oStep_exceptionalHalt _ _)
  · exact s3.trans (oStep_exceptionalHalt _ _)

theorem oResult_launchCreate {evm : Evm fork Meter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) : OResult evm result := by
  unfold launchCreate at h
  dsimp only at h
  have pre : OStep evm
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) :=
    ⟨rfl, id⟩
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact pre.trans (oStep_skipCall hs)
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 : OStep evm (recordAccountRead (accessAddress (recordAccountRead
      { evm with returnData := .empty } evm.message.currentTarget) address).2 address) :=
    (pre.trans (oStep_accessAddress _ address)).trans (oStep_recordAccountRead _ address)
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, -, hr⟩ := Base.bind_ok_iff.mp hr
    have ms : OStep evm { e2 with state } :=
      ((c0.trans (oStep_chargeStateGas h1)).trans (oStep_chargeGas h2)).trans ⟨rfl, id⟩
    split at hr
    · cases hr
      have md : OStep evm { e2 with state, gas := GasMeter.drain e2.gas } :=
        ms.trans ⟨rfl, id⟩
      exact ⟨md, fun _ _ hres => md.trans (oStep_resumeCreate hres)⟩
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      exact (ms.trans ⟨rfl, id⟩ |>.trans (oStep_pushWord h3)).advance
  · exact c0.trans (oStep_exceptionalHalt _ _)

theorem oResult_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    OResult evm result := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : OStep e3 e4 := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact oStep_popWord he
    · cases h4
      exact OStep.refl _
  have m5 : OStep evm e5 := (((((oStep_popWord h1).trans (oStep_popWord h2)).trans
    (oStep_popWord h3)).trans m4).trans (oStep_chargeGasAndMemory h5))
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact OResult.lift m5 (oResult_launchCreate h)

theorem oResult_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : OResult evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact oResult_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact oResult_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact oResult_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact oResult_createStep h
         · cases hrun)

/-- **Every step keeps the message and an output that a word can size**, and so does the caller
that resumes after a message the step sends, whatever the child. -/
theorem oResult_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : OResult evm result := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact oStep_instruction hop hr
      · split at h
        · rename_i hcall
          exact oResult_messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact oStep_controlFlowStep (op := .stop) rfl rfl

/-! ## Messages -/

/-- A precompile keeps the message, and gives an output that a word can size from call data
that a word can size. -/
theorem oStep_runPrecompile {address : Nat} {evm after : Evm fork Meter}
    (h : runPrecompile fork address evm = some after) (hd : evm.message.data.size < 2 ^ 256) :
    OStep evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact oStep_exceptionalHalt _ _
  · rename_i output hrun
    split at h
    · cases h
      exact oStep_exceptionalHalt _ _
    · cases h
      exact ⟨rfl, fun _ => size_run_lt hrun hd⟩

/-- The deposit of code keeps the output of the init code, or drops it. -/
theorem output_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) :
    after.output = evm.output ∨ after.output = .empty := by
  unfold depositCode at h
  repeat' ((try dsimp only at h); split at h)
  all_goals first
    | (cases h; first | exact .inl rfl | exact .inr rfl | (dsimp only; split <;> simp))
    | (obtain ⟨st, -, h⟩ := Base.bind_ok_iff.mp h; cases h; exact .inl rfl)

/-- What a message from call data that a word can size ends with: an output that a word can
size. -/
def OutputFits (message : Message fork) (_state : TransactionState) (_substate : Substate)
    (_meter : Meter) (ended : Evm fork Meter) : Prop :=
  message.data.size < 2 ^ 256 → ended.output.size < 2 ^ 256

/-- **Every call and creation whose call data a word can size ends with an output that a word
can size**, however deep its calls: the induction on the gas of messages. -/
theorem fits_process [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        OutputFits message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        OutputFits message state substate meter ended.val) := by
  refine processMessage_rel (R := OStep)
    (Inv := fun evm => evm.message.data.size < 2 ^ 256) (M := OutputFits)
    OStep.refl (fun hab hbc => hab.trans hbc)
    (fun {a b} ha r => by rw [r.message]; exact ha)
    (fun evm e _ => oStep_exceptionalHalt evm e)
    ?steps (fun _ _ => ⟨rfl, id⟩)
    (fun {address evm after} h hd => oStep_runPrecompile h hd)
    ?call ?create n
  case steps =>
    intro evm result _ hstep
    have r := oResult_step hstep
    cases result with
    | next after => exact r
    | child caller message resume =>
      obtain ⟨c, k⟩ := r
      exact ⟨c, fun child after hres _ => k child after hres⟩
  case call =>
    intro message state entry substate entrySubstate meter ended _ hR hd
    have fits : ended.output.size < 2 ^ 256 := (hR hd).output (by simp [startFrame])
    unfold rollbackOnError
    split <;> exact fits
  case create =>
    intro message state prepared substate meter evm after _ hM hdep hd
    rcases output_depositCode hdep with ho | ho
    · rw [ho]
      exact hM hd
    · rw [ho]
      simp

/-- **EthLib's runner of messages gives an output that a word can size**, at every fork, to a
message whose call data a word can size. -/
theorem meets_outputFits [LawfulGasMeter Meter] (fork : Fork) (bound : Nat) :
    Logic.Meets (bound := bound)
      (fun _ m child => m.data.size < 2 ^ 256 → child.output.size < 2 ^ 256)
      (Logic.processRunner fork (Meter := Meter) bound) := by
  refine ⟨fun caller m lt ended h hd => ?_, (Logic.meets_process fork bound).aborts⟩
  unfold Logic.processRunner at h
  split at h
  · exact (fits_process m.gas).1 m _ _ _ _ rfl ended h hd
  · exact (fits_process m.gas).2 m _ _ _ _ rfl ended h hd

/-- **EthLib's runner of messages at Fusaka gives an output that a word can size**, to a message
whose call data a word can size: the hypothesis that the runner of a call in its frame names. -/
theorem meets_outputFitsIn (bound : Nat) :
    EthLib.Execution.Evm.Logic.Meets (bound := bound)
      (fun _ m child => m.data.size < 2 ^ 256 → child.output.size < 2 ^ 256)
      (EthLib.Execution.Evm.Logic.processRunner .fusaka (Meter := Nat) bound) :=
  meets_outputFits .fusaka bound

/-- info: 'EthLib.Execution.Evm.OutputBound.meets_outputFitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_outputFitsIn

end EthLib.Execution.Evm.OutputBound
