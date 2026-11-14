import Contracts.UniswapV2.Factory.Core

/-!
# UniswapV2Factory.createPair in SolidCore's semantics: execution tests

The frontend translates createPair's inline assembly
`pair := create2(0, add(bytecode, 32), mload(bytecode), salt)` to `Stmt.assemblyCreate2`, so
SolidCore's checked Factory (`contract_ok`, Core.lean) has createPair. Its run is one open-world
creation request, then the call of the new pair's `initialize`. Each `#guard` runs the checked
contract's `createPair(tokenA, tokenB)` with the context's Pair creation code (`initCode`, any
bytes: the semantics takes `type(UniswapV2Pair).creationCode` from the context, which a
certificate binds to the compiler's) and answers its requests:

* the creation is CREATE2 from the factory, with the creation code as init code, value 0 and the
  salt `keccak256(abi.encodePacked(token0, token1))` of the sorted tokens (`saltWord`, by
  `cast keccak` of `0x…a1…b2`); the call is `initialize(token0, token1)` (selector `0x485cc955`)
  to the new address;
* on success: both getPair entries and `allPairs[0]` hold the pair, `allPairs.length` is 1, one
  `PairCreated(token0, token1, pair, 1)` is logged and the pair is returned;
* a failed creation (address 0) reverts with empty data: the call of `initialize` on an address
  without code fails solc's code check (negative control: the run depends on the answer);
* identical tokens revert before any request (negative control).
-/

namespace SolidCore.Verify.VC.UniswapV2Factory.Create2Run
open SolidCore.Solidity SolidCore.Solidity.Source EvmCompiler.Simulation

def initCode : List Nat := [0x60, 0x0a, 0x60, 0x0c, 0x60, 0x00, 0x39]
def factory : Nat := 0xfac
def tokenA : Nat := 0xb2
def tokenB : Nat := 0xa1
/-- `keccak256(abi.encodePacked(address(0xa1), address(0xb2)))`. -/
def saltWord : Nat := 0x40574bd1d889509cb66f9e509f7097df8329f8630487c71851b8902c58e02ee9
/-- `getPair[0xa1][0xb2]`, `getPair[0xb2][0xa1]` and `allPairs[0]` (slots 2 and 3). -/
def slot01 : Nat := 108652669453705631790926710226022211974085131167983690354478284877256485211757
def slot10 : Nat := 57201578420072540254588938014418563046356737943153306285054012880760464517709
def slotAll0 : Nat := 87903029871075914254377627908054574944891091886930582284385770809450030037083
/-- `PairCreated(address,address,address,uint256)`'s topic. -/
def pairCreated : Nat := 5975978795871356409810236859912046109003452147125615103110369160851519754473

def context (c : TypeCheck.CheckedContract) : Context :=
  { c.core.context with
    self := factory
    sender := 0x5e
    contractCreationCodes := [("UniswapV2Pair", initCode)] }

def newAccount : OpenAccount :=
  { nonce := EvmYul.UInt256.ofNat 1
    balance := EvmYul.UInt256.ofNat 0
    storage := default
    transientStorage := default
    codeBytes := ⟨#[0]⟩ }

/-- The answer to a creation: `a`, with an account with code there unless `a = 0`. -/
def created (w : OpenWorld) (a : Nat) : CreateResponse :=
  { address := EvmYul.UInt256.ofNat a
    returnData := default
    postWorld := if a = 0 then w else { w with accounts := w.accounts.insert (wordToAddress a) newAccount }
    returnedGas := EvmYul.UInt256.ofNat 0 }

def called (w : OpenWorld) : CallResponse :=
  { success := true
    returnData := default
    postWorld := w
    returnedGas := EvmYul.UInt256.ofNat 0 }

/-- A request of a run. -/
inductive Seen where
  | create (kind : CreateKind) (creator value : Nat) (initCode : List Nat) (salt : Option Nat)
  | call (target : Nat) (calldata : List Nat)
  | other
  deriving DecidableEq, Repr

/-- The end of a run: the returned words, the values of the storage slots `probe` and the number
of slots written, and the events' topics and data words; or whether a revert's data is empty. -/
inductive End where
  | returned (words : List Nat) (slots : List (Option Nat)) (size : Nat)
      (events : List (List Nat × List Nat))
  | reverted (empty : Bool)
  | stuck
  deriving DecidableEq, Repr

def words (vs : List Value) : List Nat := vs.filterMap (fun v => v.expectWord.toOption)

/-- The slots the tests read: getPair both ways, allPairs' length and first element, feeTo and
feeToSetter. -/
def probe : List Nat := [slot01, slot10, 3, slotAll0, 0, 1]

def run (a : Nat) : Nat → SolI CallResult → List Seen × End
  | 0, _ => ([], .stuck)
  | _, .done (.ok (.returned st vs)) =>
    ([], .returned (words vs) (probe.map st.storage.lookup?) st.storage.size
      (st.events.map (fun e => (e.topics, words e.data))))
  | _, .done (.ok (.reverted _ d)) => ([], .reverted (match d with | .empty => true | _ => false))
  | _, .done (.error _) => ([], .stuck)
  | n + 1, .request q k =>
    match q, k with
    | .external w (.create r), k =>
      let (rs, e) := run a n (k (created w a))
      (.create r.kind (addressToWord r.creator) (u256ToWord r.value) (r.initCode.toList.map UInt8.toNat)
        (r.salt.map u256ToWord) :: rs, e)
    | .external w (.call r), k =>
      let (rs, e) := run a n (k (called w))
      (.call (addressToWord r.codeAddress) (r.calldata.toList.map UInt8.toNat) :: rs, e)
    | _, _ => ([.other], .stuck)

def createPair (t0 t1 a : Nat) : List Seen × End :=
  match contract? with
  | .ok c =>
    match TypeCheck.CheckedContract.callFunctionWithContextTree fuel c "createPair" (context c)
        State.empty [Value.word t0, Value.word t1] with
    | some tree => run a 8 tree
    | none => ([], .stuck)
  | .error _ => ([], .stuck)

def word (n : Nat) : List Nat := (List.range 32).reverse.map (fun i => n / 256 ^ i % 256)

def creation : Seen := .create .create2 factory 0 initCode (some saltWord)

#guard createPair tokenA tokenB 0xbeef ==
  ([creation, .call 0xbeef ([0x48, 0x5c, 0xc9, 0x55] ++ word 0xa1 ++ word 0xb2)],
    .returned [0xbeef] [some 0xbeef, some 0xbeef, some 1, some 0xbeef, none, none] 4
      [([pairCreated, 0xa1, 0xb2], [0xbeef, 1])])

-- The salt is of the sorted tokens: createPair(B, A) asks the same creation.
#guard (createPair tokenB tokenA 0xbeef).1.head? == some creation

#guard createPair tokenA tokenB 0 == ([creation], .reverted true)

#guard (createPair tokenA tokenA 0xbeef).1 == []

end SolidCore.Verify.VC.UniswapV2Factory.Create2Run
