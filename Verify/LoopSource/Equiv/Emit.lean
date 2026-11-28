import Verify.LoopSource.Equiv.Inv

/-!
# Checking emitted leaves and trees in the kernel

An emitted module (`Inv.emitSeqs`, `EmitSeq.lean`) states a loop's leaves and source tree as data and
checks in the kernel that they are what `Cut.check` and the source's tree give: `resBeq` and
`treeBeq` compare by structural recursion (through `Tree.beq`), and `resBeq_eq` and `treeBeq_eq`
turn a `decide +kernel` of the comparison into the equation.
-/

namespace Verify.LoopSource.Equiv.Inv
open SolidCore.Refinement.Generic Verify.LoopSource.Equiv

/-- Equality of leaves as a `Bool`, by structural recursion, through `Tree.beq`. -/
def outBeq : Out → Out → Bool
  | .exit a, .exit b => Tree.beq a b
  | .back h, .back h' => decide (h = h')
  | _, _ => false

theorem outBeq_eq : ∀ {a b : Out}, outBeq a b = true → a = b
  | .exit _, .exit _, h => by rw [Tree.eq_of_beq h]
  | .back _, .back _, h => by rw [of_decide_eq_true h]
  | .exit _, .back _, h | .back _, .exit _, h => nomatch h

def leavesBeq : List (Facts × Out) → List (Facts × Out) → Bool
  | [], [] => true
  | p :: ps, q :: qs => decide (p.1 = q.1) && outBeq p.2 q.2 && leavesBeq ps qs
  | _, _ => false

theorem leavesBeq_eq : ∀ {a b : List (Facts × Out)}, leavesBeq a b = true → a = b
  | [], [], _ => rfl
  | p :: ps, q :: qs, h => by
    simp only [leavesBeq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [leavesBeq_eq h.2, Prod.ext h.1.1 (outBeq_eq h.1.2)]
  | [], _ :: _, h | _ :: _, [], h => nomatch h

/-- A check's result is the given leaves. -/
def resBeq (r : Option (List (Facts × Out) × List (Facts × Out))) (le li : List (Facts × Out)) : Bool :=
  match r with
  | some (a, b) => leavesBeq a le && leavesBeq b li
  | none => false

theorem resBeq_eq {r : Option (List (Facts × Out) × List (Facts × Out))} {le li : List (Facts × Out)}
    (h : resBeq r le li = true) : r = some (le, li) := by
  match r, h with
  | none, h => nomatch h
  | some (_, _), h =>
    simp only [resBeq, Bool.and_eq_true] at h
    rw [leavesBeq_eq h.1, leavesBeq_eq h.2]

/-- A tree is the given one. -/
def treeBeq (r : Option Tree) (T : Tree) : Bool :=
  match r with
  | some a => Tree.beq a T
  | none => false

theorem treeBeq_eq {r : Option Tree} {T : Tree} (h : treeBeq r T = true) : r = some T := by
  match r, h with
  | none, h => nomatch h
  | some _, h => rw [Tree.eq_of_beq h]

end Verify.LoopSource.Equiv.Inv
