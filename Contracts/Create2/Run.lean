import Contracts.Create2.Source
import Contracts.Create2.SourceView

/-!
# Inline assembly create2 in SolidCore's semantics: execution tests

`Contracts/Create2/Deployer.sol` assigns `create2(value, add(code, 32), mload(code), salt)` to a
local in inline assembly, which the frontend translates to `Stmt.assemblyCreate2` and SolidCore
runs as one open-world creation request (`emitCreate2Bytes`). Each `#guard` runs the checked
contract's function and answers its requests:

* the request is CREATE2 from the contract, with the bytes of `code` as init code, the salt and
  the value of the call, and the function returns the answered address;
* a failed creation (address 0) returns 0 and does not revert, as the EVM's CREATE2;
* the same function declared `view` is rejected by SolidCore's checker (negative control), as solc
  rejects it.
-/

namespace SolidCore.Verify.Create2.Run
open SolidCore.Solidity SolidCore.Solidity.Source EvmCompiler.Simulation

def fuel : Nat := 256
def self : Nat := 0xde91
def code : List Nat := [0x60, 0x01, 0x60, 0x0c, 0x60, 0x00, 0x39, 0x60, 0x01, 0x60, 0x00, 0xf3, 0x00]

def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract SolidCore.Verify.Create2.Source.importedSourceUnit "Deployer"

def viewContract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract SolidCore.Verify.Create2.SourceView.importedSourceUnit "Deployer"

def context (c : TypeCheck.CheckedContract) (value : Nat) : Context :=
  { c.core.context with
    self := self
    sender := 0x5e
    value := value }

/-- The creation requests of a run, answering each with `address` (and calls with success). -/
structure Seen where
  kind : CreateKind
  creator : Nat
  value : Nat
  initCode : List Nat
  salt : Option Nat
  deriving DecidableEq, Repr

def answered (w : OpenWorld) (a : Nat) : CreateResponse :=
  { address := EvmYul.UInt256.ofNat a
    returnData := default
    postWorld := w
    returnedGas := EvmYul.UInt256.ofNat 0 }

/-- The creation requests and the returned words (`none` on a revert or a stuck run). -/
def run (a : Nat) : Nat → SolI CallResult → List Seen × Option (List Nat)
  | 0, _ => ([], none)
  | _, .done (.ok (.returned _ vs)) => ([], vs.mapM (fun v => v.expectWord.toOption))
  | _, .done _ => ([], none)
  | n + 1, .request q k =>
    match q, k with
    | .external w (.create r), k =>
      let (rs, out) := run a n (k (answered w a))
      ({ kind := r.kind, creator := addressToWord r.creator, value := u256ToWord r.value,
         initCode := r.initCode.toList.map UInt8.toNat, salt := r.salt.map u256ToWord } :: rs, out)
    | _, _ => ([], none)

def call (name : String) (value : Nat) (args : List Value) (a : Nat) : List Seen × Option (List Nat) :=
  match contract? with
  | .ok c =>
    match TypeCheck.CheckedContract.callFunctionWithContextTree fuel c name (context c value)
        State.empty args with
    | some tree => run a 8 tree
    | none => ([], none)
  | .error _ => ([], none)

#guard contract?.isOk

-- `deploy(salt)`: CREATE2 of the local's bytes with value 0; it returns the new address.
#guard call "deploy" 0 [Value.fixedBytes 32 0x1234] 0xbeef ==
  ([{ kind := .create2, creator := self, value := 0, initCode := code, salt := some 0x1234 }],
    some [0xbeef])

-- A failed creation returns 0: CREATE2 never reverts the caller.
#guard call "deploy" 0 [Value.fixedBytes 32 0x1234] 0 ==
  ([{ kind := .create2, creator := self, value := 0, initCode := code, salt := some 0x1234 }],
    some [0])

-- `deployWith(v, salt, code)`: the value, the uint256 salt and the init code are the arguments.
#guard call "deployWith" 5 [Value.word 5, Value.word 7, Value.bytes [1, 2, 3]] 0xcafe ==
  ([{ kind := .create2, creator := self, value := 5, initCode := [1, 2, 3], salt := some 7 }],
    some [0xcafe])

-- Negative control: the request is the operands' and nothing else (another salt, another request).
#guard call "deploy" 0 [Value.fixedBytes 32 0x1235] 0xbeef !=
  ([{ kind := .create2, creator := self, value := 0, initCode := code, salt := some 0x1234 }],
    some [0xbeef])

-- Negative control: `deploy` declared `view` creates an account, which SolidCore's checker rejects.
#guard match viewContract? with
  | .error (.mutabilityViolation _) => true
  | _ => false

end SolidCore.Verify.Create2.Run
