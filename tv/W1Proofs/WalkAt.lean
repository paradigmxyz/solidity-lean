import SolarTV.Stages.AssemblyCheck

/-! The checker's walk on the code after the offset it reached, given the code's length.

`walk` indexes the code from its start at every instruction, so the kernel's evaluation of the
walk of a bytecode of many kilobytes takes time quadratic in its length. `walkAt` reads the
next bytes of the suffix the walk reached instead, in linear time, and `walk_of_walkAt` shows it
gives the stream `walk` gives. -/

namespace SolarTV.Assembly

def decodeAt (rest : List Nat) (len pc : Nat) : Option (Instr × Nat) :=
  match rest with
  | [] => none
  | byte :: tl =>
    if byte = PUSH0 then some (.push 0, pc + 1)
    else if PUSH1 ≤ byte ∧ byte ≤ PUSH32 then
      if pc + 1 + (byte - PUSH1 + 1) ≤ len then
        some (.push (bigEndian (tl.take (byte - PUSH1 + 1))), pc + 1 + (byte - PUSH1 + 1))
      else none
    else if hasImmediate byte then
      match tl with
      | imm :: _ => if immediateOk byte imm then some (.opImm byte imm, pc + 2) else none
      | [] => none
    else some (.op byte, pc + 1)

theorem decodeAt_eq (code : List Nat) (pc : Nat) :
    decodeAt (code.drop pc) code.length pc = decode code pc := by
  unfold decodeAt decode
  cases h : code.drop pc with
  | nil =>
    have : code.length ≤ pc := List.drop_eq_nil_iff.mp h
    simp [List.getElem?_eq_none this]
  | cons byte tl =>
    have h0 : code[pc]? = some byte := by
      have := congrArg (·[0]?) h
      simpa [List.getElem?_drop] using this
    have h1 : code.drop (pc + 1) = tl := by
      rw [← List.drop_drop, h]; rfl
    have h2 : code[pc + 1]? = tl[0]? := by
      rw [← h1, List.getElem?_drop]
    simp only [h0, h1, h2]
    cases tl <;> rfl


def Item.placedAt (rest : List Nat) (offset : Nat → Nat) (pc : Nat) : Item → Bool
  | .immutable _ bytes =>
    decide (1 ≤ bytes) && decide (bytes ≤ 32) && rest.head? == some (PUSH1 + bytes - 1)
  | item => item.placed [] offset pc

theorem Item.placedAt_eq (code : List Nat) (offset : Nat → Nat) (pc : Nat) (item : Item) :
    item.placedAt (code.drop pc) offset pc = item.placed code offset pc := by
  cases item <;> simp [Item.placedAt, Item.placed, List.head?_drop]

def walkAt (len : Nat) (offset : Nat → Nat) :
    Nat → List Nat → List Item → Option (List (Nat × Instr))
  | pc, _, [] => if pc = len then some [] else none
  | pc, rest, item :: items =>
    match decodeAt rest len pc with
    | none => none
    | some (instr, next) =>
      if instr = item.expected offset ∧ item.placedAt rest offset pc = true then
        match walkAt len offset next (rest.drop (next - pc)) items with
        | some tail => some ((pc, instr) :: tail)
        | none => none
      else none

theorem walkAt_eq (code : List Nat) (offset : Nat → Nat) :
    ∀ (pc : Nat) (items : List Item),
      walkAt code.length offset pc (code.drop pc) items = walk code offset pc items
  | pc, [] => by simp [walkAt, walk]
  | pc, item :: items => by
    simp only [walkAt, walk, decodeAt_eq, Item.placedAt_eq]
    cases hd : decode code pc with
    | none => rfl
    | some r =>
      obtain ⟨instr, next⟩ := r
      have lt := decode_advances hd
      have hdrop : (code.drop pc).drop (next - pc) = code.drop next := by
        rw [List.drop_drop]; congr 1; omega
      simp only [hdrop, walkAt_eq code offset next items]
      rfl

theorem walk_of_walkAt {code : List Nat} {len : Nat} (hl : code.length = len)
    {offset : Nat → Nat} {items : List Item} {stream : List (Nat × Instr)}
    (h : walkAt len offset 0 code items = some stream) : walk code offset 0 items = some stream := by
  subst hl
  rw [← walkAt_eq]
  simpa using h

end SolarTV.Assembly
