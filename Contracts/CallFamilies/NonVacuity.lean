import Contracts.CallFamilies.Core
import SolidCore.Refinement.SourceOracle

/-!
# The external-call families run in an open world

`Contracts/CallFamilies/Calls.sol` holds one function per external-call family of a constant-product pair
such as UniswapV2's: `sync` reads a token balance (a high-level `STATICCALL` behind solc's
`extcodesize` guard, as the pair's `sync`, `mint`, `burn` and `swap` do), `feeOn` reads the factory's
`feeTo` (the same kind of call, as `_mintFee` does), `skim` reads a balance and transfers tokens (a
low-level `CALL` whose return data must be empty or decode to `true`, as `_safeTransfer` in `skim`,
`burn` and `swap`), and `flash` transfers and then calls back (a high-level `CALL` with no return value,
as `swap`'s `uniswapV2Call`).

In the closed world of `Source.run` none of them returns normally. This module proves that in an open
world each returns normally, so that a specification proved of SolidCore under every open world
(`World.Open`) is not vacuous on any of these families:

* `witness`: an open world (`witness_open`) where the token, the factory and the callback have code,
  every transfer succeeds and returns `true`, and every other call succeeds and returns the word
  `balance`;
* `sync_returns`, `feeOn_returns`, `skim_returns`, `flash_returns`: run in `witness`, each returns
  normally;
* `sync_closed`, `skim_closed`: in the closed world neither returns normally.

Each run is the kernel's evaluation of SolidCore's interpreter (`kernel_rfl`, with the checker's
selectors from `Core`'s table), so the witnesses are proved, not tested.
-/

namespace SolidCore.Verify.VC.Calls.NonVacuity

open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement EvmCompiler.Simulation

/-- The token's address in the witness. -/
def token : Nat := 0xA0
/-- The factory's address in the witness. -/
def factory : Nat := 0xF0
/-- The callback's address in the witness. -/
def callback : Nat := 0xC0

/-- The word every call but a transfer returns: the token balance, the factory's `feeTo`. -/
def balance : Nat := 1000000

/-- The selector of `transfer(address,uint256)`, as bytes. -/
def transferSel : List Nat := [0xa9, 0x05, 0x9c, 0xbb]

/-- The return data of a call: `true` for a transfer, else the word `balance`. -/
def reply (request : CallRequest) : ByteArray :=
  if (byteArrayToBytes request.calldata).take 4 = transferSel then
    bytesToByteArray (ABI.encodeWord 1)
  else bytesToByteArray (ABI.encodeWord balance)

/-- The witness's answers: precompiles and resources as SolidCore answers them, every other call
succeeds with `reply`, every creation fails, and the world after each is the world before it. -/
def witnessAns : Ans := fun _ q =>
  match q with
  | .resource r => some (Query.defaultAnswer (.resource r))
  | .external world (.call request) =>
    match precompileAnswerCall? world request with
    | some a => some a
    | none =>
      some (show CallResponse from
        { success := true, returnData := reply request, postWorld := world,
          returnedGas := EvmYul.UInt256.ofNat 0 })
  | .external world (.create request) => some (Query.defaultAnswer (.external world (.create request)))

/-- The witness world: `witnessAns`, and code at the token, the factory and the callback. -/
def witness : World :=
  { ans := witnessAns, codes := some [(token, [0]), (factory, [0]), (callback, [0])] }

theorem witness_open : witness.Open where
  calls h world request := by
    simp only [witness, witnessAns]
    split <;> rfl
  creates _ _ _ := rfl
  precompiles h world request a ha := by
    simp only [witness, witnessAns, ha]
    rfl
  resources _ _ := rfl
  codes := rfl

/-- The contract's storage in the witness: the factory in slot 0 and the token in slot 1. -/
def storage : List (Nat × Nat) := [(0, factory), (1, token)]

/-- The call of the function with selector `sel` on the ABI-encoded arguments `args`. -/
def callOf (sel : Nat) (args : List Nat) : Call :=
  { calldata := bytesToByteArray (ABI.wordToBytesBE 4 sel ++ args), callvalue := 0, storage }

/-- `sync()`. -/
def syncCall : Call := callOf syncSel []
/-- `feeOn()`. -/
def feeOnCall : Call := callOf feeOnSel []
/-- `skim(callback)`. -/
def skimCall : Call := callOf skimSel (ABI.encodeWord callback)
/-- `flash(callback, 5, hex"01")`. -/
def flashCall : Call :=
  callOf flashSel (ABI.encodeWord callback ++ ABI.encodeWord 5 ++ ABI.encodeWord 96 ++
    ABI.encodeWord 1 ++ (1 :: List.replicate 31 0))

/-- Whether SolidCore's contract, run in `W` on `call`, returns normally. -/
def returns (W : World) (call : Call) : Bool :=
  match contract? with
  | .ok c =>
    match Source.runIn W fuel c call with
    | some obs => obs.success
    | none => false
  | .error _ => false

theorem returns_of {W : World} {call : Call} (h : returns W call = true) :
    ∃ c, contract? = .ok c ∧ ∃ obs, Source.runIn W fuel c call = some obs ∧ obs.success = true := by
  unfold returns at h
  split at h
  · next c hc =>
    refine ⟨c, hc, ?_⟩
    split at h
    · next obs hobs => exact ⟨obs, hobs, h⟩
    · simp at h
  · simp at h

theorem not_returns_of {W : World} {call : Call} (h : returns W call = false) (c)
    (hc : contract? = .ok c) : ∀ obs, Source.runIn W fuel c call = some obs → obs.success = false := by
  intro obs hobs
  unfold returns at h
  rw [hc] at h
  simp only [hobs] at h
  exact h

def syncReturns : Bool := returns witness syncCall
def feeOnReturns : Bool := returns witness feeOnCall
def skimReturns : Bool := returns witness skimCall
def flashReturns : Bool := returns witness flashCall
def syncClosed : Bool := returns World.closed syncCall
def skimClosed : Bool := returns World.closed skimCall

kernel_rfl syncReturns_eq syncReturns true using selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl feeOnReturns_eq feeOnReturns true using selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl skimReturns_eq skimReturns true using selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl flashReturns_eq flashReturns true using selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl syncClosed_eq syncClosed false using selector_eq SolidCore.Verify.VC.mkIdx_eq
kernel_rfl skimClosed_eq skimClosed false using selector_eq SolidCore.Verify.VC.mkIdx_eq

/-- **A token balance read returns in an open world**: `sync()` reaches `balanceOf` and stores it. -/
theorem sync_returns : ∃ c, contract? = .ok c ∧
    ∃ obs, Source.runIn witness fuel c syncCall = some obs ∧ obs.success = true :=
  returns_of syncReturns_eq

/-- **A factory read returns in an open world**: `feeOn()` reaches `feeTo`. -/
theorem feeOn_returns : ∃ c, contract? = .ok c ∧
    ∃ obs, Source.runIn witness fuel c feeOnCall = some obs ∧ obs.success = true :=
  returns_of feeOnReturns_eq

/-- **A transfer returns in an open world**: `skim(to)` reads the balance and transfers it. -/
theorem skim_returns : ∃ c, contract? = .ok c ∧
    ∃ obs, Source.runIn witness fuel c skimCall = some obs ∧ obs.success = true :=
  returns_of skimReturns_eq

/-- **A transfer and a callback return in an open world**: `flash` transfers, then calls back. -/
theorem flash_returns : ∃ c, contract? = .ok c ∧
    ∃ obs, Source.runIn witness fuel c flashCall = some obs ∧ obs.success = true :=
  returns_of flashReturns_eq

/-- In the closed world of `Source.run`, `sync()` never returns normally. -/
theorem sync_closed : ∀ c, contract? = .ok c →
    ∀ obs, Source.run fuel c syncCall = some obs → obs.success = false := by
  intro c hc obs h
  rw [← Source.runIn_closed] at h
  exact not_returns_of syncClosed_eq c hc obs h

/-- In the closed world of `Source.run`, `skim(to)` never returns normally. -/
theorem skim_closed : ∀ c, contract? = .ok c →
    ∀ obs, Source.run fuel c skimCall = some obs → obs.success = false := by
  intro c hc obs h
  rw [← Source.runIn_closed] at h
  exact not_returns_of skimClosed_eq c hc obs h

/-- info: 'SolidCore.Verify.VC.Calls.NonVacuity.flash_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flash_returns

/-- info: 'SolidCore.Verify.VC.Calls.NonVacuity.sync_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sync_closed

end SolidCore.Verify.VC.Calls.NonVacuity
