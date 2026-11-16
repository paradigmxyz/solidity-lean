import Verify.Lifecycle.Route
import Verify.Lifecycle.KernelIndex
import SolidCore.Refinement.KernelRfl
import Verify.Lifecycle.Examples.NoArgCtor
import Verify.Lifecycle.Examples.ArgCtor
import Verify.Lifecycle.Examples.PairCtor
import Verify.Lifecycle.Examples.ImmutableCtor

/-!
# Lifecycle regressions

The source half of the lifecycle statement, by the kernel's evaluation of `deployedAtWith` for
four constructors: no parameters (`NoArgCtor`), a `uint256` and an `address` written to two slots
(`ArgCtor`), two `uint256` parameters (`PairCtor`), and a parameter that sets an immutable, whose
value lives in the runtime bytes, not storage (`ImmutableCtor`). Each check replaces
`ABI.selectorFromSignature` by the examples' selector table (`selector_eq`) and the HashMap bucket
index by its `Nat` form (`mkIdx_eq`, Verify/Lifecycle/KernelIndex.lean). The second is what lets the
kernel evaluate SolidCore's storage at any slot count: without it every bucket index past the
first is stuck on the opaque platform word size. The storage each states is what EthLib's run of
solar's init code with the same encoded arguments leaves (the certification driver's lifecycle
probe). The negative cases show that each argument matters, that the constructors need them, that
every written slot is stated, that slots are not interchangeable, and that an immutable is not
storage.

Open: the bytecode half, `Deploys`, has no generic kernel proof yet.
-/

namespace Verify.Lifecycle.Examples

open SolidCore.Solidity Verify.Lifecycle

/-- The interpreter fuel of SolidCore's runs, as the generic source check's. -/
def fuel : Nat := 4096

/-! ## Selectors, each by Keccak-256 once, then by table -/

def selSig0 : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "get()"

kernel_rfl selSig0_eq selSig0 0x6d4ce63c

def selSig1 : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "x()"

kernel_rfl selSig1_eq selSig1 0x0c55699c

def selSig2 : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "owner()"

kernel_rfl selSig2_eq selSig2 0x8da5cb5b

def selSig3 : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "a()"

kernel_rfl selSig3_eq selSig3 0x0dbe671f

def selSig4 : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "b()"

kernel_rfl selSig4_eq selSig4 0x4df7e3d0

def selSig5 : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "limit()"

kernel_rfl selSig5_eq selSig5 0xa4d66daf

def selSig6 : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "y()"

kernel_rfl selSig6_eq selSig6 0xa56dfe4a

/-- `ABI.selectorFromSignature`, with the examples' signatures by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "get()" then 0x6d4ce63c
  else if s = "x()" then 0x0c55699c
  else if s = "owner()" then 0x8da5cb5b
  else if s = "a()" then 0x0dbe671f
  else if s = "b()" then 0x4df7e3d0
  else if s = "limit()" then 0xa4d66daf
  else if s = "y()" then 0xa56dfe4a
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split
  · next h => subst h; exact selSig0_eq
  · split
    · next h => subst h; exact selSig1_eq
    · split
      · next h => subst h; exact selSig2_eq
      · split
        · next h => subst h; exact selSig3_eq
        · split
          · next h => subst h; exact selSig4_eq
          · split
            · next h => subst h; exact selSig5_eq
            · split
              · next h => subst h; exact selSig6_eq
              · rfl

/-- Whether the contract `name` of `u` checks and its constructor, called with `ws`, leaves
exactly `s` and no logs. -/
def life? (u : SourceUnit) (name : String) (ws : List Nat) (s : List (Nat × Nat)) : Bool :=
  match TypeCheck.CheckedInput.contract u name with
  | .ok c => deployedAtWith fuel c (wordArgs ws) s
  | .error _ => false

theorem constructs_of {u : SourceUnit} {name : String} {ws : List Nat} {s : List (Nat × Nat)}
    (h : life? u name ws s = true) :
    ∃ c, TypeCheck.CheckedInput.contract u name = .ok c ∧ ∃ d, DeployedAtWith fuel c (wordArgs ws) d s := by
  unfold life? at h
  split at h
  next c hc => exact ⟨c, hc, deployedAtWith_of h⟩
  next => simp at h

/-- Whether `NoArgCtor`'s constructor, called with [], leaves exactly [(0, 7)]. -/
def noArgCtor? : Bool := life? NoArgCtor.importedSourceUnit "NoArgCtor" [] [(0, 7)]

kernel_rfl noArgCtor_eq noArgCtor? true using selector_eq mkIdx_eq

/-- `NoArgCtor` (no parameters: the constructor stores 7): SolidCore's constructor, called with [], leaves exactly [(0, 7)] and no logs. -/
theorem noArgCtor_constructs :
    ∃ c, TypeCheck.CheckedInput.contract NoArgCtor.importedSourceUnit "NoArgCtor" = .ok c ∧
      ∃ d, DeployedAtWith fuel c (wordArgs []) d [(0, 7)] :=
  constructs_of noArgCtor_eq

/-- Whether `ArgCtor`'s constructor, called with [42, 0xbeef], leaves exactly [(0, 42), (1, 48879)]. -/
def argCtor? : Bool := life? ArgCtor.importedSourceUnit "ArgCtor" [42, 0xbeef] [(0, 42), (1, 48879)]

kernel_rfl argCtor_eq argCtor? true using selector_eq mkIdx_eq

/-- `ArgCtor` (a `uint256` and an `address`: two slots): SolidCore's constructor, called with [42, 0xbeef], leaves exactly [(0, 42), (1, 48879)] and no logs. -/
theorem argCtor_constructs :
    ∃ c, TypeCheck.CheckedInput.contract ArgCtor.importedSourceUnit "ArgCtor" = .ok c ∧
      ∃ d, DeployedAtWith fuel c (wordArgs [42, 0xbeef]) d [(0, 42), (1, 48879)] :=
  constructs_of argCtor_eq

/-- Whether `PairCtor`'s constructor, called with [42, 0xbeef], leaves exactly [(0, 42), (1, 48921)]. -/
def pairCtor? : Bool := life? PairCtor.importedSourceUnit "PairCtor" [42, 0xbeef] [(0, 42), (1, 48921)]

kernel_rfl pairCtor_eq pairCtor? true using selector_eq mkIdx_eq

/-- `PairCtor` (two `uint256` parameters: `a` is the first, `b` their sum): SolidCore's constructor, called with [42, 0xbeef], leaves exactly [(0, 42), (1, 48921)] and no logs. -/
theorem pairCtor_constructs :
    ∃ c, TypeCheck.CheckedInput.contract PairCtor.importedSourceUnit "PairCtor" = .ok c ∧
      ∃ d, DeployedAtWith fuel c (wordArgs [42, 0xbeef]) d [(0, 42), (1, 48921)] :=
  constructs_of pairCtor_eq

/-- Whether `ImmutableCtor`'s constructor, called with [1000], leaves exactly [(0, 1001)]. -/
def immutableCtor? : Bool := life? ImmutableCtor.importedSourceUnit "ImmutableCtor" [1000] [(0, 1001)]

kernel_rfl immutableCtor_eq immutableCtor? true using selector_eq mkIdx_eq

/-- `ImmutableCtor` (an immutable: `limit` lives in the runtime bytes, so only `y` is stored): SolidCore's constructor, called with [1000], leaves exactly [(0, 1001)] and no logs. -/
theorem immutableCtor_constructs :
    ∃ c, TypeCheck.CheckedInput.contract ImmutableCtor.importedSourceUnit "ImmutableCtor" = .ok c ∧
      ∃ d, DeployedAtWith fuel c (wordArgs [1000]) d [(0, 1001)] :=
  constructs_of immutableCtor_eq

/-- Another first argument does not leave the same storage. -/
def argCtorOther? : Bool := life? ArgCtor.importedSourceUnit "ArgCtor" [41, 0xbeef] [(0, 42), (1, 48879)]

kernel_rfl argCtorOther_eq argCtorOther? false using selector_eq mkIdx_eq

/-- Another address does not leave the same storage. -/
def argCtorOwner? : Bool := life? ArgCtor.importedSourceUnit "ArgCtor" [42, 0xbeee] [(0, 42), (1, 48879)]

kernel_rfl argCtorOwner_eq argCtorOwner? false using selector_eq mkIdx_eq

/-- The parameterized constructor has no deployment without its arguments. -/
def argCtorNoArgs? : Bool := life? ArgCtor.importedSourceUnit "ArgCtor" [] [(0, 42), (1, 48879)]

kernel_rfl argCtorNoArgs_eq argCtorNoArgs? false using selector_eq mkIdx_eq

/-- Leaving out a written slot is not exactly the storage. -/
def argCtorOneSlot? : Bool := life? ArgCtor.importedSourceUnit "ArgCtor" [42, 0xbeef] [(0, 42)]

kernel_rfl argCtorOneSlot_eq argCtorOneSlot? false using selector_eq mkIdx_eq

/-- Another second argument changes the sum. -/
def pairCtorOther? : Bool := life? PairCtor.importedSourceUnit "PairCtor" [42, 0xbeee] [(0, 42), (1, 48921)]

kernel_rfl pairCtorOther_eq pairCtorOther? false using selector_eq mkIdx_eq

/-- Slots are not interchangeable. -/
def pairCtorSwapped? : Bool := life? PairCtor.importedSourceUnit "PairCtor" [42, 0xbeef] [(0, 48921), (1, 42)]

kernel_rfl pairCtorSwapped_eq pairCtorSwapped? false using selector_eq mkIdx_eq

/-- Another argument does not leave the same storage. -/
def immutableOther? : Bool := life? ImmutableCtor.importedSourceUnit "ImmutableCtor" [999] [(0, 1001)]

kernel_rfl immutableOther_eq immutableOther? false using selector_eq mkIdx_eq

/-- The parameterized constructor has no deployment without its argument. -/
def immutableNoArgs? : Bool := life? ImmutableCtor.importedSourceUnit "ImmutableCtor" [] [(0, 1001)]

kernel_rfl immutableNoArgs_eq immutableNoArgs? false using selector_eq mkIdx_eq

/-- The immutable is not stored: claiming it in slot 0 fails. -/
def immutableStored? : Bool := life? ImmutableCtor.importedSourceUnit "ImmutableCtor" [1000] [(0, 1000)]

kernel_rfl immutableStored_eq immutableStored? false using selector_eq mkIdx_eq

end Verify.Lifecycle.Examples
