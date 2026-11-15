import Contracts.CallFamilies.Stage0
import SolidCore.Refinement.KernelThm

/-!
# `sync` in solar's first lowered MIR, for every oracle

`sem_sync`: solar's stage0 of `Contracts/CallFamilies/Calls.sol` (`SolarTV.Export.Calls.stage0`, `-Ogas`,
osaka) runs `sync()` from the storage `σ` to `mirEnd o σ` under every oracle `o`: it reads the
token (slot 1), makes one `STATICCALL` of `balanceOf(address(this))` (world `W o σ`), reverts with
the callee's return data when the call fails, reverts with empty data when it returned fewer than
32 bytes, and otherwise stores the returned word in slot 2. Each block step is the kernel's
conversion (`kernel_thm`); the steps whose guard depends on the oracle are split by cases.
-/

open SolidCore.Refinement.Kernel
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered

namespace SolidCore.Refinement.CallFamilies.Sync

set_option linter.deprecated false

def syncCall (σ : List (Nat × Nat)) : Call :=
  { calldata := ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩, callvalue := 0, storage := σ }

abbrev step (o : Oracle) (σ : List (Nat × Nat)) := moduleBlock o (syncCall σ) SolarTV.Export.Calls.stage0

def next {ς : Type} (st : ς → Option ((Halt × State) ⊕ ς)) (x : ς) : ς :=
  match st x with
  | some (.inr y) => y
  | _ => x

def F0 (σ : List (Nat × Nat)) : Frame := ([], .enter 10 0 0, fun _ => 0, State.initial (syncCall σ))
def F1 (o : Oracle) (σ : List (Nat × Nat)) : Frame := next (step o σ) (F0 σ)
def F2 (o : Oracle) (σ : List (Nat × Nat)) : Frame := next (step o σ) (F1 o σ)
def F3 (o : Oracle) (σ : List (Nat × Nat)) : Frame := next (step o σ) (F2 o σ)
def F4 (o : Oracle) (σ : List (Nat × Nat)) : Frame := next (step o σ) (F3 o σ)

kernel_thm h0 : ∀ (o : Oracle) (σ : List (Nat × Nat)), step o σ (F0 σ) = some (.inr (F1 o σ))
kernel_thm h1 : ∀ (o : Oracle) (σ : List (Nat × Nat)), step o σ (F1 o σ) = some (.inr (F2 o σ))
kernel_thm h2 : ∀ (o : Oracle) (σ : List (Nat × Nat)), step o σ (F2 o σ) = some (.inr (F3 o σ))
kernel_thm h3 : ∀ (o : Oracle) (σ : List (Nat × Nat)), step o σ (F3 o σ) = some (.inr (F4 o σ))

def mem1 : Mem :=
  ((Mem.initial.store 64 128).store 0 0x70a08231).store 32 (BitVec.ofNat 256 environment.callee)

def input : List Memory.Byte := ((mem1.expand 28 36).expand 0 32).read 28 36

def W (o : Oracle) (σ : List (Nat × Nat)) : List Event :=
  [.read "gas", .call .staticcall [o.env "gas" [.read "gas"] [], BitVec.ofNat 256 (slotValue σ 1)] input
    (State.initial (syncCall σ)).storage (fun _ => 0)]

def M4 (o : Oracle) (σ : List (Nat × Nat)) : Mem :=
  ((mem1.expand 28 36).expand 0 32).write 0 (min 32 (returndataSize o (W o σ)).toNat)
    (returndataByte o (W o σ))

def S4 (o : Oracle) (σ : List (Nat × Nat)) : State :=
  ⟨M4 o σ, (State.initial (syncCall σ)).storage, fun _ => 0, W o σ⟩

kernel_thm F4_eq : ∀ (o : Oracle) (σ : List (Nat × Nat)), F4 o σ =
    ([], .enter 4 0 (if callFlag o (W o σ) = 0 then 1 else 2), (F4 o σ).2.2.1, S4 o σ)

def G2 (o : Oracle) (σ : List (Nat × Nat)) (env : Env) : Frame := ([], .enter 4 0 2, env, S4 o σ)
def G2n (o : Oracle) (σ : List (Nat × Nat)) (env : Env) : Frame := next (step o σ) (G2 o σ env)

kernel_thm g2 : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env), step o σ (G2 o σ env) = some (.inr (G2n o σ env))
kernel_thm G2n_eq : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env), G2n o σ env =
    ([], .enter 4 2 (if EvmRules.Evm.lt (returndataSize o (W o σ)) 32 = 0 then 4 else 3), (G2n o σ env).2.2.1, S4 o σ)

kernel_thm g3 : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env),
    step o σ ([], .enter 4 2 3, env, S4 o σ) = some (.inl (halt (S4 o σ) 0 0 true))

kernel_thm g4 : ∀ (o : Oracle) (σ : List (Nat × Nat)) (env : Env),
    step o σ ([], .enter 4 2 4, env, S4 o σ) = some (.inl (.stop,
      { S4 o σ with memory := (M4 o σ).expand 0 32,
                    storage := update (S4 o σ).storage 2 ((M4 o σ).load 0) }))

def syncFn : Function := (SolarTV.Export.Calls.stage0.functions[4]?).getD ⟨[], [], none⟩
kernel_thm fn4 : SolarTV.Export.Calls.stage0.functions[4]? = some syncFn
kernel_thm b1 : syncFn.blocks[1]? = some ⟨[],
    [.effect (some 23) .returndatasize [],
     .effect none .returndatacopy [.const 0, .const 0, .value 23],
     .effect (some 24) .returndatasize []],
    .revert (.const 0) (.value 24)⟩

theorem exec_b1 (o : Oracle) (call : Call) (env : Env) (s : State) :
    execInsts o call [.effect (some 23) .returndatasize [],
     .effect none .returndatacopy [.const 0, .const 0, .value 23],
     .effect (some 24) .returndatasize []] env s =
    some ((env.set 23 (returndataSize o s.world)).set 24 (returndataSize o s.world),
      { s with memory := s.memory.write 0 (returndataSize o s.world).toNat (fun i => returndataByte o s.world (0 + i)) }) := by
  simp only [execInsts, Effect.apply, List.map_cons, List.map_nil, Operand.eval]
  have h : (env.set 23 (returndataSize o s.world)) 23 = returndataSize o s.world := by
    simp [Env.set]
  simp only [h, returndataSize]
  simp

theorem g1 (o : Oracle) (σ : List (Nat × Nat)) (env : Env) :
    step o σ ([], .enter 4 0 1, env, S4 o σ) = some (.inl (halt
      { S4 o σ with memory := (M4 o σ).write 0 (returndataSize o (W o σ)).toNat (fun i => returndataByte o (W o σ) (0 + i)) } 0 (returndataSize o (W o σ)) true)) := by
  simp only [step, moduleBlock, fn4, b1, bindPhis, segment, splitCall, exec_b1]
  simp [Operand.eval, Env.set, S4]

theorem iter_next {ς : Type} {st : ς → Option ((Halt × State) ⊕ ς)} {n : Nat} {x y : ς}
    (h : st x = some (.inr y)) : iterate st (n + 1) x = iterate st n y := by
  conv => lhs; unfold iterate
  rw [h]

theorem iter_end {ς : Type} {st : ς → Option ((Halt × State) ⊕ ς)} {n : Nat} {x : ς} {r : Halt × State}
    (h : st x = some (.inl r)) : iterate st (n + 1) x = some r := by
  conv => lhs; unfold iterate
  rw [h]

/-- The end of solar's stage0 on a call of sync. -/
def mirEnd (o : Oracle) (σ : List (Nat × Nat)) : Halt × State :=
  if callFlag o (W o σ) = 0 then
    halt { S4 o σ with memory := (M4 o σ).write 0 (returndataSize o (W o σ)).toNat (fun i => returndataByte o (W o σ) (0 + i)) } 0 (returndataSize o (W o σ)) true
  else if EvmRules.Evm.lt (returndataSize o (W o σ)) 32 = 0 then
    (.stop, { S4 o σ with memory := (M4 o σ).expand 0 32, storage := update (S4 o σ).storage 2 ((M4 o σ).load 0) })
  else halt (S4 o σ) 0 0 true

theorem run_sync (o : Oracle) (σ : List (Nat × Nat)) :
    Module.run o SolarTV.Export.Calls.stage0 (syncCall σ) 7 = some (mirEnd o σ) := by
  show iterate (step o σ) 7 (F0 σ) = _
  rw [iter_next (h0 o σ), iter_next (h1 o σ), iter_next (h2 o σ), iter_next (h3 o σ), F4_eq]
  unfold mirEnd
  by_cases hf : callFlag o (W o σ) = 0
  · rw [if_pos hf, if_pos hf, iter_end (g1 o σ _)]
  · rw [if_neg hf, if_neg hf]
    have e : (([], .enter 4 0 2, (F4 o σ).2.2.1, S4 o σ) : Frame) = G2 o σ (F4 o σ).2.2.1 := rfl
    rw [e, iter_next (g2 o σ _), G2n_eq]
    by_cases hl : EvmRules.Evm.lt (returndataSize o (W o σ)) 32 = 0
    · rw [if_pos hl, if_pos hl, iter_end (g4 o σ _)]
    · rw [if_neg hl, if_neg hl, iter_end (g3 o σ _)]

theorem sem_sync (o : Oracle) (σ : List (Nat × Nat)) :
    (moduleSem o).run SolarTV.Export.Calls.stage0 (syncCall σ) =
      some (observe (syncCall σ) (mirEnd o σ).2 (mirEnd o σ).1) := by
  show (moduleLayer.result o _ _).map _ = _
  rw [moduleLayer.result_of_ends (show moduleLayer.Ends o SolarTV.Export.Calls.stage0 (syncCall σ) (mirEnd o σ) from ⟨7, run_sync o σ⟩)]
  rfl

/-- info: 'SolidCore.Refinement.CallFamilies.Sync.sem_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sem_sync

end SolidCore.Refinement.CallFamilies.Sync
