import W1Proofs.Segment

/-! # Segments of a recursive function's stages

The relations of a recursive function's stages (tools/certify/rec_cuts.py) bound the EVM IR stack
below a frame by the recursion's measure (the words every frame below keeps, times the measure,
under a constant that leaves room for the frame itself under the 1024-word limit), so that no
segment of either program overflows the stack. Their relation lemmas then ask for such bounds
besides configurations: `rec_seg` is `sym_seg` whose relation lemmas may also close a bound
`a ≤ b` over stack lengths and words' numbers, by `omega` over `toNat`s as `sym_omega` does.
Nothing else differs; every step is checked by the kernel. -/

namespace SolarTV.Milestone.W1

/-- A bound over stack lengths and words' numbers, from the cases split so far. -/
macro "rec_bound" : tactic => `(tactic| (
  (try dsimp only [MIR.Lowered.Env.set, iteNatLit, ↓reduceIte] at *)
  (try simp only [List.length_cons, List.length_nil, List.length_append, Nat.reduceAdd] at *)
  sym_omega))

/-- What a relation lemma asks of the target configuration (`seg_eq`), and bounds. -/
macro "rec_eq" : tactic => `(tactic| (
  repeat (apply Exists.intro)
  repeat' (apply And.intro)
  all_goals first
    | seg_word_eq
    | rec_bound))

syntax "rec_cut" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| rec_cut []) => `(tactic| fail "rec_seg: no relation relates the cut points")
  | `(tactic| rec_cut [$m]) => `(tactic| (refine $m ?_; rec_eq))
  | `(tactic| rec_cut [$m, $ms,*]) => `(tactic|
      first
        | (refine $m ?_; rec_eq)
        | rec_cut [$ms,*])

/-- `sym_seg` with relation lemmas that may ask for bounds (`rec_cut`). -/
syntax "rec_seg" "[" Lean.Parser.Tactic.simpLemma,* "]" "[" ident,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rec_seg [$us,*] [$ms,*]) => `(tactic| (
      obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
      seg_norm [$us,*]
      repeat' (split_cond <;> seg_norm [$us,*])
      all_goals first
        | exact True.intro
        | (apply agree_of_eq; seg_eq)
        | rec_cut [$ms,*]
        | (exfalso; bv_omega)
        | (exfalso; sym_omega)
        | (exfalso; sym_comm_contra)
        | (exfalso; rec_bound)
        | fail "rec_seg: the segments end differently on this path, or the procedure cannot tell"))

end SolarTV.Milestone.W1
