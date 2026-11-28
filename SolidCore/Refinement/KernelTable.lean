/-!
# Lookup tables for kernel checks

A generated module replaces a costly function of strings, such as Keccak-256 of a signature,
by a table of the values it needs, each checked once in a declaration of its own (see
SolidCore/Refinement/KernelRfl.lean, `kernel_rfl ... using`). `tableOr f t` is `f` with the
entries of `t` read from the table, and `eq_tableOr` proves `f = tableOr f t` from one equation
per entry, so a module states its table as data and proves the replacement in one line, whatever
the number of entries.
-/

namespace SolidCore.Refinement.KernelTable

universe u

/-- `f`, with the entries of `t` read from the table: the value of the first key equal to `s`,
else `f s`. -/
def tableOr {α : Type u} (f : String → α) : List (String × α) → String → α
  | [], s => f s
  | (k, v) :: t, s => if s = k then v else tableOr f t s

/-- Each entry of the table is `f`'s value at its key. -/
def Agrees {α : Type u} (f : String → α) : List (String × α) → Prop
  | [] => True
  | (k, v) :: t => f k = v ∧ Agrees f t

/-- A table whose entries agree with `f` replaces `f`. -/
theorem eq_tableOr {α : Type u} {f : String → α} :
    ∀ {t : List (String × α)}, Agrees f t → f = tableOr f t
  | [], _ => rfl
  | (k, _) :: _, ⟨hk, ht⟩ => funext fun s => by
    by_cases h : s = k
    · subst h; simp only [tableOr]; exact hk
    · simp only [tableOr, h, ↓reduceIte]; exact congrFun (eq_tableOr ht) s

end SolidCore.Refinement.KernelTable
