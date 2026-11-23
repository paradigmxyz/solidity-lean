import Verify.Spec.HashScopeFinite

/-!
# The address-level storage frame of an ERC20 call, from the finite premise

An ERC20 call's target postcondition frames storage by slot: every slot \`n\` other than the slots the
call writes keeps its value,

  \`∀ n, n % 2 ^ 256 ≠ w₁ → … → s' n = s n\`.

A reader wants the frame by address: \`balanceOf[k]\` is unchanged for every account \`k\` the call
does not name, and so is every allowance it does not write. Between the two sits keccak256: the
slot of \`balanceOf[k]\` is \`solHash k b\`, the slot of \`allowance[o][p]\` is
\`solHash p (solHash o a)\`, and that a slot the call writes is none of these is a fact about keccak256
on their preimages.

This file derives the address-level frame from the finite premise of Verify/Spec/HashScopeFinite.lean,
\`KeccakSep (erc20Preimages b a A)\`: keccak256 injective, with images at least \`2 ^ 128\`, on the
preimages an ERC20 with balances at slot \`b\` and allowances at slot \`a\` hashes for the finite set \`A\`
of addresses. No universal separation is assumed, and every conclusion is about keys in \`A\`:

* \`transfer_frame\`: \`transfer\` from \`c\` to \`t\` (\`c, t ∈ A\`, \`c = t\` included) leaves
  \`balanceOf[k]\` for every \`k ∈ A\` other than \`c\` and \`t\`, and every \`allowance[o][p]\` with
  \`o, p ∈ A\`; \`transfer_balance_frame\` is its balance half, from the balance preimages alone;
* \`transferFrom_frame\`: \`transferFrom(f, t)\` sent by \`c\` (writing \`balanceOf[f]\`, \`balanceOf[t]\` and
  \`allowance[f][c]\`) leaves every other balance of \`A\` and every allowance of \`A\` but
  \`allowance[f][c]\`;
* \`approve_frame\`: \`approve(p₀)\` sent by \`c\` (writing \`allowance[c][p₀]\`) leaves every balance of \`A\`
  and every allowance of \`A\` but \`allowance[c][p₀]\`.

Premises: \`A\`'s addresses are below \`2 ^ 160\`, \`b < 2 ^ 128\` (an allowance slot is not a balance slot
because its inner key, a keccak256 image, is at least \`2 ^ 128\`), \`a < 2 ^ 256\`. The storage functions
\`s s' : Nat → Nat\` are arbitrary: the theorems are about the frame's shape, not about any contract.

Negative controls: \`written_slot_not_framed\` (the slot frame says nothing about the caller's own
slot: a storage pair satisfies it and changes \`balanceOf[c]\`), \`outside_key_not_separated\` (a hash
separated on the balance preimages of \`{addrA, addrB}\` can send \`addrC\`'s balance slot onto
\`addrA\`'s, so nothing follows for a key outside \`A\`), and \`frame_rejects_caller_and_outside\`
(\`transfer_frame\` does not elaborate at \`k = c\` or at \`k ∉ A\`).
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic TrustedBase

/-! ## Slot facts on a separated set -/

theorem solHash_mod (k m : Nat) : solHash k m % 2 ^ 256 = solHash k m :=
  Nat.mod_eq_of_lt (solHash_lt k m)

/-- Two slots whose preimages lie in a separated set are equal only for the same key and slot. -/
theorem keccakSep_inj {S : Finset (List Nat)} (h : KeccakSep S) {x y m n : Nat}
    (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) (hm : m < 2 ^ 256) (hn : n < 2 ^ 256)
    (hxS : mappingPreimage x m ∈ S) (hyS : mappingPreimage y n ∈ S)
    (he : solHash x m = solHash y n) : x = y ∧ m = n := by
  rw [solHash_eq, solHash_eq] at he
  exact mappingPreimage_inj hx hy hm hn (h.1 _ _ hxS hyS he)

/-- A slot whose preimage lies in a separated set is at least \`2 ^ 128\`. -/
theorem keccakSep_ge {S : Finset (List Nat)} (h : KeccakSep S) {x m : Nat}
    (hxS : mappingPreimage x m ∈ S) : 2 ^ 128 ≤ solHash x m := by
  rw [solHash_eq]; exact h.2 _ hxS

/-- The inner preimage of \`allowance[o][p]\`, its key written as SolidCore's slot \`solHash o a\`. -/
theorem inner_mem' {b a : Nat} {A : Finset Nat} {o p : Nat} (ho : o ∈ A) (hp : p ∈ A) :
    mappingPreimage p (solHash o a) ∈ erc20Preimages b a A := by
  rw [solHash_eq]; exact inner_mem ho hp

theorem balance_mem_bal {b : Nat} {A : Finset Nat} {k : Nat} (hk : k ∈ A) :
    mappingPreimage k b ∈ balancePreimages b A :=
  Finset.mem_image_of_mem (fun k => mappingPreimage k b) hk

theorem balancePreimages_sub (b a : Nat) (A : Finset Nat) :
    balancePreimages b A ⊆ erc20Preimages b a A :=
  Finset.subset_union_left

/-- **Distinct accounts of \`A\` have distinct balance slots.** -/
theorem bal_ne_bal {b : Nat} {A : Finset Nat} (h : KeccakSep (balancePreimages b A))
    (hA : ∀ x ∈ A, x < 2 ^ 160) (hb : b < 2 ^ 256) {k c : Nat} (hk : k ∈ A) (hc : c ∈ A)
    (hne : k ≠ c) : solHash k b ≠ solHash c b := fun he =>
  hne (keccakSep_inj h (lt_trans (hA k hk) (by decide)) (lt_trans (hA c hc) (by decide)) hb hb
    (balance_mem_bal hk) (balance_mem_bal hc) he).1

/-- **No allowance slot of \`A\` is a balance slot of \`A\`**: equal slots would give equal inner keys,
\`solHash o a = b\`, but the left side is at least \`2 ^ 128\` and \`b\` is below it. -/
theorem allow_ne_bal {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A))
    (hA : ∀ x ∈ A, x < 2 ^ 160) (hb : b < 2 ^ 128) {o p k : Nat} (ho : o ∈ A) (hp : p ∈ A)
    (hk : k ∈ A) : solHash p (solHash o a) ≠ solHash k b := fun he => by
  have hge := keccakSep_ge h (outer_mem (b := b) ho)
  have := (keccakSep_inj h (lt_trans (hA p hp) (by decide)) (lt_trans (hA k hk) (by decide))
    (solHash_lt o a) (lt_trans hb (by decide)) (inner_mem' ho hp) (balance_mem hk) he).2
  omega

/-- **Distinct allowance entries of \`A\` have distinct slots**: equal slots give the same spender and
equal outer slots, hence the same owner. -/
theorem allow_ne_allow {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A))
    (hA : ∀ x ∈ A, x < 2 ^ 160) (ha : a < 2 ^ 256) {o p o' p' : Nat} (ho : o ∈ A) (hp : p ∈ A)
    (ho' : o' ∈ A) (hp' : p' ∈ A) (hne : o ≠ o' ∨ p ≠ p') :
    solHash p (solHash o a) ≠ solHash p' (solHash o' a) := fun he => by
  obtain ⟨hpp, hoa⟩ := keccakSep_inj h (lt_trans (hA p hp) (by decide))
    (lt_trans (hA p' hp') (by decide)) (solHash_lt o a) (solHash_lt o' a) (inner_mem' ho hp)
    (inner_mem' ho' hp') he
  have hoo := (keccakSep_inj h (lt_trans (hA o ho) (by decide)) (lt_trans (hA o' ho') (by decide))
    ha ha (outer_mem (b := b) ho) (outer_mem (b := b) ho') hoa).1
  rcases hne with hne | hne
  · exact hne hoo
  · exact hne hpp

/-! ## transfer -/

/-- **transfer's balance frame by address**: if \`s'\` agrees with \`s\` off the balance slots of \`c\` and
\`t\`, then for every \`k ∈ A\` other than \`c\` and \`t\`, \`balanceOf[k]\` is unchanged. Needs only the
balance preimages of \`A\`. -/
theorem transfer_balance_frame {b : Nat} {A : Finset Nat} (h : KeccakSep (balancePreimages b A))
    (hA : ∀ x ∈ A, x < 2 ^ 160) (hb : b < 2 ^ 256) {c t : Nat} (hc : c ∈ A) (ht : t ∈ A)
    {s s' : Nat → Nat}
    (hfr : ∀ n, n % 2 ^ 256 ≠ solHash c b → n % 2 ^ 256 ≠ solHash t b → s' n = s n) :
    ∀ k ∈ A, k ≠ c → k ≠ t → s' (solHash k b) = s (solHash k b) := fun k hk hkc hkt =>
  hfr _ (by rw [solHash_mod]; exact bal_ne_bal h hA hb hk hc hkc)
    (by rw [solHash_mod]; exact bal_ne_bal h hA hb hk ht hkt)

/-- **transfer from \`c\` to \`t\`, the address-level frame** (\`c, t ∈ A\`, \`c = t\` included): from the
slot frame, \`balanceOf[k]\` is unchanged for every \`k ∈ A\` other than \`c\` and \`t\`, and
\`allowance[o][p]\` is unchanged for every \`o, p ∈ A\`. -/
theorem transfer_frame {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A))
    (hA : ∀ x ∈ A, x < 2 ^ 160) (hb : b < 2 ^ 128) {c t : Nat} (hc : c ∈ A) (ht : t ∈ A)
    {s s' : Nat → Nat}
    (hfr : ∀ n, n % 2 ^ 256 ≠ solHash c b → n % 2 ^ 256 ≠ solHash t b → s' n = s n) :
    (∀ k ∈ A, k ≠ c → k ≠ t → s' (solHash k b) = s (solHash k b)) ∧
      ∀ o ∈ A, ∀ p ∈ A, s' (solHash p (solHash o a)) = s (solHash p (solHash o a)) :=
  ⟨transfer_balance_frame (h.mono (balancePreimages_sub b a A)) hA (lt_trans hb (by decide)) hc ht
      hfr,
    fun _ ho _ hp => hfr _ (by rw [solHash_mod]; exact allow_ne_bal h hA hb ho hp hc)
      (by rw [solHash_mod]; exact allow_ne_bal h hA hb ho hp ht)⟩

/-! ## transferFrom -/

/-- **transferFrom(f, t) sent by \`c\`, the address-level frame** (\`f, t, c ∈ A\`, equal addresses
included): the call writes \`balanceOf[f]\`, \`balanceOf[t]\` and \`allowance[f][c]\`; from the slot frame
over those three slots, \`balanceOf[k]\` is unchanged for every \`k ∈ A\` other than \`f\` and \`t\`, and
\`allowance[o][p]\` for every \`o, p ∈ A\` with \`(o, p) ≠ (f, c)\`. -/
theorem transferFrom_frame {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A))
    (hA : ∀ x ∈ A, x < 2 ^ 160) (hb : b < 2 ^ 128) (ha : a < 2 ^ 256) {f t c : Nat} (hf : f ∈ A)
    (ht : t ∈ A) (hc : c ∈ A) {s s' : Nat → Nat}
    (hfr : ∀ n, n % 2 ^ 256 ≠ solHash f b → n % 2 ^ 256 ≠ solHash t b →
      n % 2 ^ 256 ≠ solHash c (solHash f a) → s' n = s n) :
    (∀ k ∈ A, k ≠ f → k ≠ t → s' (solHash k b) = s (solHash k b)) ∧
      ∀ o ∈ A, ∀ p ∈ A, (o ≠ f ∨ p ≠ c) →
        s' (solHash p (solHash o a)) = s (solHash p (solHash o a)) := by
  have hbal := h.mono (balancePreimages_sub b a A)
  have hbw : b < 2 ^ 256 := lt_trans hb (by decide)
  refine ⟨fun k hk hkf hkt => hfr _ ?_ ?_ ?_, fun o ho p hp hne => hfr _ ?_ ?_ ?_⟩ <;>
    rw [solHash_mod]
  · exact bal_ne_bal hbal hA hbw hk hf hkf
  · exact bal_ne_bal hbal hA hbw hk ht hkt
  · exact Ne.symm (allow_ne_bal h hA hb hf hc hk)
  · exact allow_ne_bal h hA hb ho hp hf
  · exact allow_ne_bal h hA hb ho hp ht
  · exact allow_ne_allow h hA ha ho hp hf hc hne

/-! ## approve -/

/-- **approve(p₀) sent by \`c\`, the address-level frame** (\`c, p₀ ∈ A\`): the call writes
\`allowance[c][p₀]\`; from the slot frame over that slot, \`balanceOf[k]\` is unchanged for every
\`k ∈ A\`, and \`allowance[o][p]\` for every \`o, p ∈ A\` with \`(o, p) ≠ (c, p₀)\`. -/
theorem approve_frame {b a : Nat} {A : Finset Nat} (h : KeccakSep (erc20Preimages b a A))
    (hA : ∀ x ∈ A, x < 2 ^ 160) (hb : b < 2 ^ 128) (ha : a < 2 ^ 256) {c p₀ : Nat} (hc : c ∈ A)
    (hp₀ : p₀ ∈ A) {s s' : Nat → Nat}
    (hfr : ∀ n, n % 2 ^ 256 ≠ solHash p₀ (solHash c a) → s' n = s n) :
    (∀ k ∈ A, s' (solHash k b) = s (solHash k b)) ∧
      ∀ o ∈ A, ∀ p ∈ A, (o ≠ c ∨ p ≠ p₀) →
        s' (solHash p (solHash o a)) = s (solHash p (solHash o a)) :=
  ⟨fun _ hk => hfr _ (by rw [solHash_mod]; exact Ne.symm (allow_ne_bal h hA hb hc hp₀ hk)),
    fun _ ho _ hp hne => hfr _ (by rw [solHash_mod]; exact allow_ne_allow h hA ha ho hp hc hp₀ hne)⟩

/-! ## Negative controls -/

/-- **The slot frame says nothing about a written slot**: for every \`b\`, \`c\`, \`t\` there are storages
\`s\`, \`s'\` that satisfy transfer's slot frame and change \`balanceOf[c]\`. So \`transfer_frame\` with
\`k = c\` allowed is false, whatever premise on keccak256. -/
theorem written_slot_not_framed (b c t : Nat) :
    ∃ s s' : Nat → Nat,
      (∀ n, n % 2 ^ 256 ≠ solHash c b → n % 2 ^ 256 ≠ solHash t b → s' n = s n) ∧
        s' (solHash c b) ≠ s (solHash c b) :=
  ⟨fun _ => 0, fun n => if n % 2 ^ 256 = solHash c b then 1 else 0,
    fun n h1 _ => ite_eq_right_iff.2 fun h => absurd h h1, by
      show (if solHash c b % 2 ^ 256 = solHash c b then 1 else 0) ≠ 0
      rw [solHash_mod, if_pos rfl]
      decide⟩

/-- **The premise on \`A\` says nothing outside \`A\`**: a hash separated on the balance preimages of
\`{addrA, addrB}\` (injective, images at least \`2 ^ 128\`) can send \`addrC\`'s balance preimage onto
\`addrA\`'s image, so no argument from it frames \`balanceOf[addrC]\`. -/
theorem outside_key_not_separated :
    ∃ hash : List Nat → Nat,
      SeparatedBy hash [mappingPreimage addrA 1, mappingPreimage addrB 1] ∧
        hash (mappingPreimage addrC 1) = hash (mappingPreimage addrA 1) :=
  ⟨fun x => if x = mappingPreimage addrB 1 then 2 ^ 128 + 1 else 2 ^ 128,
    (separatedBy_iff_check _ _).2 (by decide +kernel), by decide +kernel⟩

/-- **\`transfer_frame\` refuses the caller's own slot and a key outside \`A\`**: at the three addresses
of \`addrsABC\`, the frame of \`addrC\`'s balance in a transfer from \`addrA\` to \`addrB\` elaborates; at
\`k = addrA\` (the caller) the side condition \`addrA ≠ addrA\` cannot be shown, and with
\`A = {addrA, addrB}\` the key \`addrC\` is not in \`A\`. \`fail_if_success\` keeps this file building only
while both are refused. -/
theorem frame_rejects_caller_and_outside (h : KeccakSep (erc20Preimages 1 2 addrsABC))
    (_h2 : KeccakSep (erc20Preimages 1 2 {addrA, addrB})) {s s' : Nat → Nat}
    (hfr : ∀ n, n % 2 ^ 256 ≠ solHash addrA 1 → n % 2 ^ 256 ≠ solHash addrB 1 → s' n = s n) :
    True := by
  have hA : ∀ x ∈ addrsABC, x < 2 ^ 160 := by decide
  have hA2 : ∀ x ∈ ({addrA, addrB} : Finset Nat), x < 2 ^ 160 := by decide
  have _hC : s' (solHash addrC 1) = s (solHash addrC 1) :=
    (transfer_frame (a := 2) h hA (by decide) (by decide) (by decide) hfr).1 addrC (by decide)
      (by decide) (by decide)
  fail_if_success
    have _hcaller : s' (solHash addrA 1) = s (solHash addrA 1) :=
      (transfer_frame (a := 2) h hA (by decide) (by decide) (by decide) hfr).1 addrA (by decide)
        (by decide) (by decide)
  fail_if_success
    have _hout : s' (solHash addrC 1) = s (solHash addrC 1) :=
      (transfer_frame (a := 2) _h2 hA2 (by decide) (by decide) (by decide) hfr).1 addrC (by decide)
        (by decide) (by decide)
  trivial

/-- The frame of the three addresses at the real keccak256 (\`real_erc20_ABC\`): a transfer from
\`addrA\` to \`addrB\` leaves \`balanceOf[addrC]\` and every allowance among the three. -/
theorem real_transfer_frame_ABC {s s' : Nat → Nat}
    (hfr : ∀ n, n % 2 ^ 256 ≠ solHash addrA 1 → n % 2 ^ 256 ≠ solHash addrB 1 → s' n = s n) :
    s' (solHash addrC 1) = s (solHash addrC 1) ∧
      ∀ o ∈ addrsABC, ∀ p ∈ addrsABC, s' (solHash p (solHash o 2)) = s (solHash p (solHash o 2)) :=
  have hf := transfer_frame real_erc20_ABC (by decide) (by decide) (by decide) (by decide) hfr
  ⟨hf.1 addrC (by decide) (by decide) (by decide), hf.2⟩

/-! ## Axiom checks -/

/-- info: 'SolidCore.Spec.keccakSep_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccakSep_inj

/-- info: 'SolidCore.Spec.bal_ne_bal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bal_ne_bal

/-- info: 'SolidCore.Spec.allow_ne_bal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allow_ne_bal

/-- info: 'SolidCore.Spec.allow_ne_allow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allow_ne_allow

/-- info: 'SolidCore.Spec.transfer_balance_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_balance_frame

/-- info: 'SolidCore.Spec.transfer_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_frame

/-- info: 'SolidCore.Spec.transferFrom_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transferFrom_frame

/-- info: 'SolidCore.Spec.approve_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms approve_frame

/-- info: 'SolidCore.Spec.written_slot_not_framed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms written_slot_not_framed

/-- info: 'SolidCore.Spec.outside_key_not_separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms outside_key_not_separated

/-- info: 'SolidCore.Spec.frame_rejects_caller_and_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_rejects_caller_and_outside

/-- info: 'SolidCore.Spec.real_transfer_frame_ABC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms real_transfer_frame_ABC

end SolidCore.Spec
