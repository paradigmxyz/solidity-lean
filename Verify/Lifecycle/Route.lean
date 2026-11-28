import SolidCore.Refinement.Wide.Refines
import SolidCore.Refinement.Deploy

/-!
# Lifecycle: construction with arguments

`Wide.DeployedAt` checks what a contract's constructor leaves when it is run with no
arguments, so a contract whose constructor takes parameters has no deployed storage there. This
module gives the argument-aware route and the lifecycle statement the certification driver's
lifecycle tier states, in three parts that follow a creation:

1. initcode: `initArgs initcode ws` is the code a creation runs, solar's init code followed by
   the ABI encoding of the static argument words `ws` (32 bytes each, as Solidity appends
   constructor arguments to the creation code).
2. runtime bytes: `Deploys (initArgs initcode ws) code s` says EthLib runs that code in the
   creation frame to success and returns `code`, the runtime bytecode the creation installs. With
   immutables this is not solar's `bin-runtime` output, whose immutable slots are placeholders the
   constructor fills, so the statement is about the returned bytes.
3. storage after construction: EthLib's run leaves the storage `s`, and SolidCore's constructor,
   called with the argument values `wordArgs ws`, leaves exactly the entries `s` and no logs
   (`DeployedAtWith`).

`DeployedAtWith fuel c [] d s` is `Wide.DeployedAt fuel c d s` (`deployedAt_iff_nil`), so the
no-argument route is the special case it was. `deployedAtWith` is the Boolean check a kernel
conversion proves, as `deployedAt` is for the no-argument route, and `deployedAtWith_of` its
soundness.

Not covered: arguments other than static words (dynamic types such as `bytes` or `string`), the
creation message's address derivation and the code deposit, as in `SolidCore.Refinement.Deploy`.
-/

namespace Verify.Lifecycle

open EthLib.Base SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Wide

/-- The constructor argument values of the static argument words `ws`. -/
def wordArgs (ws : List Nat) : List TypeCheck.CoreValue := ws.map Value.word

/-- The ABI encoding of the static argument words `ws`: 32 big-endian bytes each. -/
def argBytes (ws : List Nat) : ByteArray := ⟨(ws.flatMap fun w => natToBytes 32 w).toArray⟩

/-- The code a creation of `initcode` with the argument words `ws` runs. -/
def initArgs (initcode : ByteArray) (ws : List Nat) : ByteArray := initcode ++ argBytes ws

/-- What the constructor of `c`, called with `args`, leaves: the state `d`, whose storage holds
exactly the entries `s`, with no logs. -/
structure DeployedAtWith (fuel : Nat) (c : TypeCheck.CheckedContract) (args : List TypeCheck.CoreValue)
    (d : Source.State) (s : List (Nat × Nat)) : Prop where
  cons : ∃ vs, TypeCheck.CheckedContract.constructWithContext? fuel c (ctxOf c) State.empty
    selfAddress 0 args = some (CallResult.returned d vs)
  storage : d.storage.toList = s
  events : d.events = []

/-- Whether the constructor of `c`, called with `args`, leaves exactly the storage entries `s` and
no logs. -/
def deployedAtWith (fuel : Nat) (c : TypeCheck.CheckedContract) (args : List TypeCheck.CoreValue)
    (s : List (Nat × Nat)) : Bool :=
  match TypeCheck.CheckedContract.constructWithContext? fuel c (ctxOf c) State.empty selfAddress
      0 args with
  | some (CallResult.returned d _) => d.storage.toList == s && d.events.isEmpty
  | _ => false

theorem deployedAtWith_of {fuel : Nat} {c : TypeCheck.CheckedContract}
    {args : List TypeCheck.CoreValue} {s : List (Nat × Nat)}
    (h : deployedAtWith fuel c args s = true) : ∃ d, DeployedAtWith fuel c args d s := by
  unfold deployedAtWith at h
  split at h
  next d vs hc =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    exact ⟨d, ⟨vs, hc⟩, h.1, h.2⟩
  next => simp at h

/-- With no arguments the route is `Wide.DeployedAt`. -/
theorem deployedAt_iff_nil {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} : DeployedAt fuel c d s ↔ DeployedAtWith fuel c [] d s :=
  ⟨fun h => ⟨h.cons, h.storage, h.events⟩, fun h => ⟨h.cons, h.storage, h.events⟩⟩

/-- The Boolean checks agree with no arguments. -/
theorem deployedAtWith_nil (fuel : Nat) (c : TypeCheck.CheckedContract) (s : List (Nat × Nat)) :
    deployedAtWith fuel c [] s = deployedAt fuel c s := rfl

/-- No arguments append nothing to the init code. -/
theorem initArgs_nil (initcode : ByteArray) : initArgs initcode [] = initcode := by
  apply ByteArray.ext
  simp [initArgs, argBytes]

/-- Each argument word adds 32 bytes to the creation code. -/
theorem argBytes_size (ws : List Nat) : (argBytes ws).size = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [argBytes, ByteArray.size, List.size_toArray, List.flatMap_cons, List.length_append,
      natToBytes_length, List.length_cons] at ih ⊢
    omega

/-- **The lifecycle statement** of a contract `c` compiled to init code `initcode`, created
with the static argument words `ws`: EthLib runs the init code with the encoded arguments
appended to success and returns the runtime bytecode `code` with the storage `s`, and SolidCore's
constructor on the same arguments leaves exactly the storage `s` and no logs. -/
structure Statement (fuel : Nat) (c : TypeCheck.CheckedContract) (initcode code : ByteArray)
    (ws : List Nat) (s : List (Nat × Nat)) : Prop where
  deploys : Deploys (initArgs initcode ws) code s
  source : ∃ d, DeployedAtWith fuel c (wordArgs ws) d s

/-- The source half of a lifecycle statement from the Boolean check. -/
theorem source_of {fuel : Nat} {c : TypeCheck.CheckedContract} {ws : List Nat}
    {s : List (Nat × Nat)} (h : deployedAtWith fuel c (wordArgs ws) s = true) :
    ∃ d, DeployedAtWith fuel c (wordArgs ws) d s :=
  deployedAtWith_of h

end Verify.Lifecycle
