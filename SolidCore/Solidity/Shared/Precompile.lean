import SolidCore.Solidity.Shared.Call
import SolidCore.Solidity.Shared.PrecompileCrypto

namespace SolidCore.Solidity.Shared
namespace Precompile

abbrev Byte := Call.Byte
abbrev Bytes := Call.Bytes
abbrev Result := Call.Result Call.ExternalCallKind

def wordBytes : Nat := 32

def byte (value : Nat) : Byte :=
  Account.byte value

def normalizeBytes : Bytes → Bytes :=
  Account.normalizeBytes

def bytesToWordBE (bytes : Bytes) : Word :=
  SolidCore.Solidity.Shared.norm
    (bytes.foldl (fun acc b => acc * 256 + byte b) 0)

def bytesToNatBE (bytes : Bytes) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + byte b) 0

def wordToBytesBE : Nat -> Word -> Bytes
  | 0, _ => []
  | n + 1, value =>
      wordToBytesBE n (value / 256) ++ [byte value]

def wordBytesBE (value : Word) : Bytes :=
  wordToBytesBE wordBytes value

def readWord? (bytes : Bytes) (offset : Nat) : Option Word :=
  let rest := (normalizeBytes bytes).drop offset
  if wordBytes <= rest.length then
    some (bytesToWordBE (rest.take wordBytes))
  else
    none

def natOfSliceRightPadded (bytes : Bytes) (offset width : Nat) : Nat :=
  let slice := (normalizeBytes bytes).drop offset |>.take width
  bytesToNatBE slice * 256 ^ (width - slice.length)

inductive Kind where
  | ecrecover
  | sha256
  | ripemd160
  | identity
  | modexp
  | bnAdd
  | bnMul
  | bnPairing
  | blake2f
  | pointEvaluation
  deriving Repr, BEq, DecidableEq

def address : Kind -> Word
  | Kind.ecrecover => 1
  | Kind.sha256 => 2
  | Kind.ripemd160 => 3
  | Kind.identity => 4
  | Kind.modexp => 5
  | Kind.bnAdd => 6
  | Kind.bnMul => 7
  | Kind.bnPairing => 8
  | Kind.blake2f => 9
  | Kind.pointEvaluation => 10

def mainnetKinds : List Kind :=
  [ Kind.ecrecover
  , Kind.sha256
  , Kind.ripemd160
  , Kind.identity
  , Kind.modexp
  , Kind.bnAdd
  , Kind.bnMul
  , Kind.bnPairing
  , Kind.blake2f
  , Kind.pointEvaluation ]

-- Precompile answering (constraint, not history): precompile calls still EMIT
-- ordinary `Query.external` staticcall nodes — the query alphabet is the
-- transcript-alignment surface with evm-compiler and must keep matching it —
-- but their ANSWERS are computed in-semantics (`execute?` below), consulted by
-- the interpreter's answering folds ONLY on a responder-row miss (row-first
-- precedence: a scripted row for a precompile address keeps answering exactly
-- as before). Kinds without a sound in-model implementation return `none` and
-- stay fail-closed open-world, exactly as an arbitrary contract call.

def callKind : Call.ExternalCallKind :=
  Call.ExternalCallKind.staticcall

def successfulStaticcall (kind : Kind) (input output : Bytes)
    (gas? : Option Word := none) : Result :=
  { kind := callKind
    target := address kind
    calldata := normalizeBytes input
    value := 0
    gas? := gas?
    success := true
    output := normalizeBytes output }

def identityStaticcall (input : Bytes) (gas? : Option Word := none) :
    Result :=
  successfulStaticcall Kind.identity input input (gas? := gas?)

def expModAux (modulus acc base exponent : Nat) : Nat :=
  if h : exponent = 0 then
    if modulus == 0 then 0 else acc % modulus
  else
    let acc' :=
      if exponent % 2 == 1 then
        (acc * base) % modulus
      else
        acc % modulus
    let base' := (base * base) % modulus
    expModAux modulus acc' base' (exponent / 2)
termination_by exponent
decreasing_by
  have hpos : 0 < exponent := Nat.pos_of_ne_zero h
  exact Nat.div_lt_self hpos (by decide : 1 < 2)

def expMod (modulus base exponent : Nat) : Nat :=
  expModAux modulus 1 base exponent

def modexpInput (base exponent modulus : Bytes) : Bytes :=
  wordBytesBE base.length ++
    wordBytesBE exponent.length ++
    wordBytesBE modulus.length ++
    normalizeBytes base ++
    normalizeBytes exponent ++
    normalizeBytes modulus

def modexpOutput (input : Bytes) : Bytes :=
  let input := normalizeBytes input
  let baseLength := natOfSliceRightPadded input 0 wordBytes
  let exponentLength := natOfSliceRightPadded input wordBytes wordBytes
  let modulusLength := natOfSliceRightPadded input (2 * wordBytes) wordBytes
  let base := natOfSliceRightPadded input (3 * wordBytes) baseLength
  let exponent :=
    natOfSliceRightPadded input (3 * wordBytes + baseLength)
      exponentLength
  let modulus :=
    natOfSliceRightPadded input
      (3 * wordBytes + baseLength + exponentLength) modulusLength
  if modulusLength == 0 || modulus == 0 then
    List.replicate modulusLength 0
  else
    wordToBytesBE modulusLength (expMod modulus base exponent)

def modexpStaticcall (input : Bytes) (gas? : Option Word := none) :
    Result :=
  successfulStaticcall Kind.modexp input (modexpOutput input) (gas? := gas?)

def builtinStaticcallResult? (kind : Call.ExternalCallKind)
    (target : Word) (calldata : Bytes) (value : Word)
    (gas? : Option Word) : Option Result :=
  if kind == callKind &&
      Call.wordEq target (address Kind.identity) &&
      Call.wordEq value 0 then
    some (identityStaticcall calldata (gas? := gas?))
  else if kind == callKind &&
      Call.wordEq target (address Kind.modexp) &&
      Call.wordEq value 0 then
    some (modexpStaticcall calldata (gas? := gas?))
  else
    none

/-- The precompile `Kind` living at word `w`, if any. -/
def kindOfAddress? (w : Word) : Option Kind :=
  mainnetKinds.find? (fun kind => Call.wordEq (address kind) w)

/-- Fail-closed bound on each modexp length header. Real gas metering
    (EIP-2565) bounds mainnet-reachable operand sizes; the gas-free model
    refuses (`none` → open-world fail-closed) above this bound rather than
    model unbounded work. -/
def modexpLengthCap : Nat := 4096

/-- The in-semantics precompile answer: `some (success, output)` when the
    kind is answered in-model, `none` (fail-closed, stays open-world) for
    unimplemented kinds (bnPairing 0x8, pointEvaluation 0xa) and for
    resource-capped inputs (modexp length headers over `modexpLengthCap`,
    blake2f rounds over `Crypto.blake2fRoundsCap`). `success = false` is a
    genuine precompile ERROR (bnAdd/bnMul invalid point, malformed blake2f
    input) — a failed staticcall, exactly mainnet's. Output/input bytes are
    normalized. -/
def execute? (kind : Kind) (input : Bytes) : Option (Bool × Bytes) :=
  let input := normalizeBytes input
  match kind with
  | Kind.ecrecover => some (true, Crypto.ecrecoverBytes input)
  | Kind.sha256 => some (true, Crypto.sha256Bytes input)
  | Kind.ripemd160 =>
      some (true, List.replicate 12 0 ++ Crypto.ripemd160Bytes input)
  | Kind.identity => some (true, input)
  | Kind.modexp =>
      let baseLength := natOfSliceRightPadded input 0 wordBytes
      let exponentLength := natOfSliceRightPadded input wordBytes wordBytes
      let modulusLength :=
        natOfSliceRightPadded input (2 * wordBytes) wordBytes
      if baseLength <= modexpLengthCap &&
          exponentLength <= modexpLengthCap &&
          modulusLength <= modexpLengthCap then
        some (true, modexpOutput input)
      else
        none
  | Kind.bnAdd =>
      match Crypto.bnAddBytes? input with
      | some output => some (true, output)
      | none => some (false, [])
  | Kind.bnMul =>
      match Crypto.bnMulBytes? input with
      | some output => some (true, output)
      | none => some (false, [])
  | Kind.blake2f => Crypto.blake2fBytes? input
  | Kind.bnPairing => none
  | Kind.pointEvaluation => none


def outputWord? (result : Result) : Option Word :=
  if result.success then
    readWord? result.output 0
  else
    none

def ecrecoverInput (digest v r s : Word) : Bytes :=
  wordBytesBE digest ++ wordBytesBE v ++ wordBytesBE r ++ wordBytesBE s

end Precompile
end SolidCore.Solidity.Shared
