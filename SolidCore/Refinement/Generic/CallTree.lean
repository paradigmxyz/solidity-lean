import SolidCore.Refinement.Generic.CanonCmp
import SolarTV.Machine

/-!
# The call node of the generic source stage

A function of the call fragment makes at most one external call on each path. `CTree` is the
outcome of such a call of it: branches on words (`ite`) and plain trees (`tree`, a path with no
external call) before the call, and the call itself (`call r ws n t`):

* `r : CReq` is the request: a `STATICCALL` (`static`) or a `CALL`, its target and value words
  and its input bytes, all words of the call before the external one;
* `ws` are the storage writes made before it, so the callee sees the caller's storage
  `Writes.store ρ ws`;
* on success the call goes on as the plain tree `t`, read over the valuation `ρ.withAns n a`:
  the call's `n` argument words, then the answer's words (`ansWords`: the size of the return
  data modulo `2 ^ 256`, then its words, big-endian, zero past its end);
* on failure the call reverts with the callee's return data and changes nothing (Solidity's
  bubbling of a failed call without `try`).

What the callee answers is a parameter of the semantics, `Callee`: a function of the evaluated
request and of the caller's storage when it is sent. `CTree.eval ρ A` is the result of the call
when the callee answers as `A` does. The stage that uses it instantiates `A` with the world's
answer on the source side and the oracle's on the target side, and proves that they agree on the
request the path reaches.

`CTree.agree` compares two call trees: their structure, their branch words, requests, writes at
the call and continuations by `Tree.agree` (`CTree.agree_sound`), after `CTree.prep` takes
branches on constants and splits disjunctions (`CTree.eval_prep`).
-/

namespace SolidCore.Refinement.Generic

/-! ## Requests and answers -/

/-- The request of an external call: its kind (`STATICCALL` when `static`, else `CALL`), the
target and value words, and the input bytes. -/
structure CReq where
  static : Bool
  target : WExpr
  value : WExpr
  input : List OByte
  deriving DecidableEq, Repr

/-- The request's values on a call. -/
structure CReqV where
  static : Bool
  target : Nat
  value : Nat
  input : List Nat
  deriving DecidableEq

def CReq.eval (ρ : Val) (r : CReq) : CReqV :=
  ⟨r.static, r.target.eval ρ, r.value.eval ρ, r.input.map (OByte.eval ρ)⟩

/-- A callee's answer: whether the call succeeded, and its return data. -/
structure CAns where
  ok : Bool
  data : List Nat

/-- What the callee answers a request, given the caller's storage when it is sent. -/
abbrev Callee := CReqV → (Nat → Nat) → CAns

/-- The bytes of a byte string as a machine memory, zero past its end. -/
def dataMem (data : List Nat) : SolarTV.Machine.Mem := ⟨fun i => BitVec.ofNat 8 (data.getD i 0), 0⟩

/-- The big-endian word of the 32 bytes of `data` from `off`, zero past its end, as `MLOAD`
reads them. -/
def wordAt (data : List Nat) (off : Nat) : Nat := ((dataMem data).load off).toNat

/-- The words a call's continuation reads of its answer: the size of the return data modulo
`2 ^ 256`, then its words. -/
def ansWords (a : CAns) : List Nat :=
  (a.data.length % wordSize) ::
    (List.range ((a.data.length + 31) / 32)).map fun k => wordAt a.data (32 * k)

/-- The valuation of a call's continuation: the call's `n` argument words, then the answer's
words; the same storage, hash and caller. -/
def Val.withAns (ρ : Val) (n : Nat) (a : CAns) : Val :=
  { ρ with args := (List.range n).map (fun i => ρ.args.getD i 0) ++ ansWords a }

theorem getD_append_range (ρ : Val) (n : Nat) (rest : List Nat) (i : Nat) (hi : i < n) :
    ((List.range n).map (fun i => ρ.args.getD i 0) ++ rest).getD i 0 = ρ.args.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
  simp [List.getElem?_range hi]

theorem getD_append_range_ge (ρ : Val) (n : Nat) (rest : List Nat) (j : Nat) :
    ((List.range n).map (fun i => ρ.args.getD i 0) ++ rest).getD (n + j) 0 = rest.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem withAns_arg (ρ : Val) (n : Nat) (a : CAns) {i : Nat} (hi : i < n) :
    (ρ.withAns n a).args.getD i 0 = ρ.args.getD i 0 :=
  getD_append_range ρ n _ i hi

theorem withAns_size (ρ : Val) (n : Nat) (a : CAns) :
    (ρ.withAns n a).args.getD n 0 = a.data.length % wordSize := by
  have := getD_append_range_ge ρ n (ansWords a) 0
  simp [Val.withAns, ansWords] at this ⊢

theorem withAns_word (ρ : Val) (n : Nat) (a : CAns) {k : Nat} (hk : 32 * k < a.data.length) :
    (ρ.withAns n a).args.getD (n + 1 + k) 0 = wordAt a.data (32 * k) := by
  have := getD_append_range_ge ρ n (ansWords a) (k + 1)
  rw [show n + (k + 1) = n + 1 + k by omega] at this
  simp only [Val.withAns]
  rw [this]
  simp only [ansWords, List.getD_cons_succ]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

@[simp] theorem withAns_store (ρ : Val) (n : Nat) (a : CAns) : (ρ.withAns n a).store = ρ.store := rfl
@[simp] theorem withAns_hash (ρ : Val) (n : Nat) (a : CAns) : (ρ.withAns n a).hash = ρ.hash := rfl
@[simp] theorem withAns_caller (ρ : Val) (n : Nat) (a : CAns) :
    (ρ.withAns n a).caller = ρ.caller := rfl

theorem Val.Ok.withAns {ρ : Val} (h : ρ.Ok) (n : Nat) (a : CAns) : (ρ.withAns n a).Ok := h

/-! ## Call trees -/

/-- The outcome of a call of a function that makes at most one external call on each path. -/
inductive CTree where
  /-- A path with no external call. -/
  | tree (t : Tree)
  | ite (c : WExpr) (a b : CTree)
  /-- The external call `r`, sent with the caller's storage after the writes `ws`; on success
  the plain tree `t` over the answer's words after the `n` argument words. -/
  | call (r : CReq) (ws : Writes) (n : Nat) (t : Tree)
  deriving DecidableEq, Repr

/-- The result of a failed external call that is not caught: a revert with the callee's return
data, which changes nothing. -/
def bubbleRes (ρ : Val) (a : CAns) : Res :=
  { success := false, output := a.data, logs := [], store := ρ.store }

/-- The result of a call when the callee answers as `A`. -/
def CTree.eval (ρ : Val) (A : Callee) : CTree → Res
  | .tree t => t.eval ρ
  | .ite c a b => if c.eval ρ = 0 then b.eval ρ A else a.eval ρ A
  | .call r ws n t =>
    if (A (r.eval ρ) (Writes.store ρ ws)).ok then t.eval (ρ.withAns n (A (r.eval ρ) (Writes.store ρ ws)))
    else bubbleRes ρ (A (r.eval ρ) (Writes.store ρ ws))

/-- The external call the path of `ρ` reaches, if any: its request, the writes before it and the
number of argument words. -/
def CTree.reach (ρ : Val) : CTree → Option (CReq × Writes × Nat)
  | .tree _ => none
  | .ite c a b => if c.eval ρ = 0 then b.reach ρ else a.reach ρ
  | .call r ws n _ => some (r, ws, n)

/-- Two callees that answer the request the path reaches alike give the same result. -/
theorem CTree.eval_congr (ρ : Val) {A B : Callee} : ∀ (T : CTree),
    (∀ r ws n, T.reach ρ = some (r, ws, n) →
      A (r.eval ρ) (Writes.store ρ ws) = B (r.eval ρ) (Writes.store ρ ws)) →
    T.eval ρ A = T.eval ρ B
  | .tree _, _ => rfl
  | .ite c a b, h => by
    simp only [CTree.eval]
    by_cases h0 : c.eval ρ = 0
    · simp only [h0, ↓reduceIte]
      exact CTree.eval_congr ρ b (fun r ws n hr => h r ws n (by simp [CTree.reach, h0, hr]))
    · simp only [h0, ↓reduceIte]
      exact CTree.eval_congr ρ a (fun r ws n hr => h r ws n (by simp [CTree.reach, h0, hr]))
  | .call r ws n t, h => by
    simp only [CTree.eval, h r ws n rfl]

/-! ## Preparing a call tree for comparison: constant branches, disjunctions -/

/-- A branch on a word that is not a disjunction, taken when the word is a constant. -/
def cbranch (c : WExpr) (t e : CTree) : CTree :=
  match c.norm.lit? with
  | some v => if v % wordSize = 0 then e else t
  | none => .ite c t e

theorem cbranch_eval (ρ : Val) (A : Callee) (c : WExpr) (t e : CTree) :
    (cbranch c t e).eval ρ A = if c.eval ρ = 0 then e.eval ρ A else t.eval ρ A := by
  unfold cbranch
  split
  · rename_i v hv
    have hc := WExpr.eval_norm ρ c
    rw [WExpr.eq_of_lit? hv] at hc
    simp only [WExpr.eval] at hc
    rw [← hc]
    by_cases h : v % wordSize = 0 <;> simp [h]
  · rfl

theorem cbranch_reach (ρ : Val) (c : WExpr) (t e : CTree) :
    (cbranch c t e).reach ρ = if c.eval ρ = 0 then e.reach ρ else t.reach ρ := by
  unfold cbranch
  split
  · rename_i v hv
    have hc := WExpr.eval_norm ρ c
    rw [WExpr.eq_of_lit? hv] at hc
    simp only [WExpr.eval] at hc
    rw [← hc]
    by_cases h : v % wordSize = 0 <;> simp [h]
  · rfl

/-- A branch on `c` of call trees, its disjunctions split, its constants taken. -/
def csplitCond : WExpr → CTree → CTree → CTree
  | .bin .or a b, t, e => csplitCond a t (csplitCond b t e)
  | c, t, e => cbranch c t e

theorem csplitCond_eval (ρ : Val) (A : Callee) : ∀ (c : WExpr) (t e : CTree),
    (csplitCond c t e).eval ρ A = if c.eval ρ = 0 then e.eval ρ A else t.eval ρ A
  | .bin .or a b, t, e => by
    simp only [csplitCond, csplitCond_eval ρ A a, csplitCond_eval ρ A b, or_eval_eq_zero]
    by_cases ha : a.eval ρ = 0 <;> by_cases hb : b.eval ρ = 0 <;> simp [ha, hb]
  | .lit _, t, e => cbranch_eval ρ A _ t e
  | .arg _, t, e => cbranch_eval ρ A _ t e
  | .init _, t, e => cbranch_eval ρ A _ t e
  | .caller, t, e => cbranch_eval ρ A _ t e
  | .un _ _, t, e => cbranch_eval ρ A _ t e
  | .sinit _, t, e => cbranch_eval ρ A _ t e
  | .sel _ _ _, t, e => cbranch_eval ρ A _ t e
  | .hash _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .add _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .sub _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .mul _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .div _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .lt _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .gt _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .eq _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .and _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .xor _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .shl _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .shr _ _, t, e => cbranch_eval ρ A _ t e
  | .bin .byte _ _, t, e => cbranch_eval ρ A _ t e

theorem csplitCond_reach (ρ : Val) : ∀ (c : WExpr) (t e : CTree),
    (csplitCond c t e).reach ρ = if c.eval ρ = 0 then e.reach ρ else t.reach ρ
  | .bin .or a b, t, e => by
    simp only [csplitCond, csplitCond_reach ρ a, csplitCond_reach ρ b, or_eval_eq_zero]
    by_cases ha : a.eval ρ = 0 <;> by_cases hb : b.eval ρ = 0 <;> simp [ha, hb]
  | .lit _, t, e => cbranch_reach ρ _ t e
  | .arg _, t, e => cbranch_reach ρ _ t e
  | .init _, t, e => cbranch_reach ρ _ t e
  | .caller, t, e => cbranch_reach ρ _ t e
  | .un _ _, t, e => cbranch_reach ρ _ t e
  | .sinit _, t, e => cbranch_reach ρ _ t e
  | .sel _ _ _, t, e => cbranch_reach ρ _ t e
  | .hash _ _, t, e => cbranch_reach ρ _ t e
  | .bin .add _ _, t, e => cbranch_reach ρ _ t e
  | .bin .sub _ _, t, e => cbranch_reach ρ _ t e
  | .bin .mul _ _, t, e => cbranch_reach ρ _ t e
  | .bin .div _ _, t, e => cbranch_reach ρ _ t e
  | .bin .lt _ _, t, e => cbranch_reach ρ _ t e
  | .bin .gt _ _, t, e => cbranch_reach ρ _ t e
  | .bin .eq _ _, t, e => cbranch_reach ρ _ t e
  | .bin .and _ _, t, e => cbranch_reach ρ _ t e
  | .bin .xor _ _, t, e => cbranch_reach ρ _ t e
  | .bin .shl _ _, t, e => cbranch_reach ρ _ t e
  | .bin .shr _ _, t, e => cbranch_reach ρ _ t e
  | .bin .byte _ _, t, e => cbranch_reach ρ _ t e

/-- A call tree with every branch's disjunctions split and its constants taken. -/
def CTree.prep : CTree → CTree
  | .tree t => .tree t
  | .ite c a b => csplitCond c a.prep b.prep
  | .call r ws n t => .call r ws n t

theorem CTree.eval_prep (ρ : Val) (A : Callee) : ∀ T : CTree, T.prep.eval ρ A = T.eval ρ A
  | .tree _ => rfl
  | .ite c a b => by
    simp only [CTree.prep, csplitCond_eval, CTree.eval, CTree.eval_prep ρ A a, CTree.eval_prep ρ A b]
  | .call _ _ _ _ => rfl

theorem CTree.reach_prep (ρ : Val) : ∀ T : CTree, T.prep.reach ρ = T.reach ρ
  | .tree _ => rfl
  | .ite c a b => by
    simp only [CTree.prep, csplitCond_reach, CTree.reach, CTree.reach_prep ρ a, CTree.reach_prep ρ b]
  | .call _ _ _ _ => rfl

/-! ## Comparing call trees -/

/-- A branch word as a tree: success exactly when the word is not zero. -/
def condTree (c : WExpr) : Tree := .ite c (.halt true [] [] []) (.halt false [] [] [])

/-- A request as a tree: its input as the output, its target and value as the words of slots 0
and 1. -/
def reqTree (r : CReq) : Tree := .halt true r.input [(.lit 0, r.target), (.lit 1, r.value)] []

/-- Storage writes as a tree. -/
def wsTree (ws : Writes) : Tree := .halt true [] ws []

theorem condTree_zero {c c' : WExpr} (h : Tree.agree (condTree c) (condTree c') = true) (ρ : Val) :
    c.eval ρ = 0 ↔ c'.eval ρ = 0 := by
  have e := congrArg Res.success (Tree.eval_of_agree h ρ)
  simp only [condTree, Tree.eval] at e
  by_cases h1 : c.eval ρ = 0 <;> by_cases h2 : c'.eval ρ = 0 <;> simp_all

theorem reqTree_eval {r r' : CReq} (hs : r.static = r'.static)
    (h : Tree.agree (reqTree r) (reqTree r') = true) (ρ : Val) : r.eval ρ = r'.eval ρ := by
  have e := Tree.eval_of_agree h ρ
  simp only [reqTree, Tree.eval, ↓reduceIte, Res.mk.injEq] at e
  obtain ⟨-, hin, -, hst⟩ := e
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  have hz : (0 : Nat) % wordSize = 0 := rfl
  have ho : (1 : Nat) % wordSize = 1 := by decide
  have hz1 : ¬ ((0 : Nat) = 1) := by decide
  simp only [Writes.store, WExpr.eval, hz, ho, ↓reduceIte, hz1] at h0 h1
  simp only [CReq.eval, hs, h0, h1, hin]

theorem wsTree_eval {ws ws' : Writes} (h : Tree.agree (wsTree ws) (wsTree ws') = true) (ρ : Val) :
    Writes.store ρ ws = Writes.store ρ ws' := by
  have e := Tree.eval_of_agree h ρ
  simp only [wsTree, Tree.eval, ↓reduceIte, Res.mk.injEq] at e
  exact e.2.2.2

/-- Whether two prepared call trees agree: the same structure, with branch words, requests, writes
at the call and plain trees that `Tree.agree` relates. -/
def CTree.agreeP : CTree → CTree → Bool
  | .tree a, .tree b => Tree.agree a b
  | .ite c a b, .ite c' a' b' =>
    Tree.agree (condTree c) (condTree c') && CTree.agreeP a a' && CTree.agreeP b b'
  | .call r ws n t, .call r' ws' n' t' =>
    (r.static == r'.static) && (n == n') && Tree.agree (reqTree r) (reqTree r') &&
      Tree.agree (wsTree ws) (wsTree ws') && Tree.agree t t'
  | _, _ => false

/-- What agreeing call trees share on every call: the same result for every callee, and the same
request and writes at the call the path reaches (up to their values) and argument count. -/
theorem CTree.agreeP_sound : ∀ {T1 T2 : CTree}, CTree.agreeP T1 T2 = true → ∀ (ρ : Val) (A : Callee),
    T1.eval ρ A = T2.eval ρ A ∧
      (∀ r ws n, T1.reach ρ = some (r, ws, n) → ∃ r' ws', T2.reach ρ = some (r', ws', n) ∧
        r.eval ρ = r'.eval ρ ∧ Writes.store ρ ws = Writes.store ρ ws') ∧
      (∀ r ws n, T2.reach ρ = some (r, ws, n) → ∃ r' ws', T1.reach ρ = some (r', ws', n) ∧
        r.eval ρ = r'.eval ρ ∧ Writes.store ρ ws = Writes.store ρ ws')
  | .tree a, .tree b, h, ρ, A => by
    simp only [CTree.agreeP] at h
    exact ⟨Tree.eval_of_agree h ρ, fun r ws n hr => by simp [CTree.reach] at hr,
      fun r ws n hr => by simp [CTree.reach] at hr⟩
  | .ite c a b, .ite c' a' b', h, ρ, A => by
    simp only [CTree.agreeP, Bool.and_eq_true] at h
    obtain ⟨⟨hc, ha⟩, hb⟩ := h
    have hz := condTree_zero hc ρ
    have sa := CTree.agreeP_sound ha ρ A
    have sb := CTree.agreeP_sound hb ρ A
    by_cases h0 : c.eval ρ = 0
    · have h0' : c'.eval ρ = 0 := hz.mp h0
      simp only [CTree.eval, CTree.reach, h0, h0', ↓reduceIte]
      exact sb
    · have h0' : ¬ c'.eval ρ = 0 := fun h => h0 (hz.mpr h)
      simp only [CTree.eval, CTree.reach, h0, h0', ↓reduceIte]
      exact sa
  | .call r ws n t, .call r' ws' n' t', h, ρ, A => by
    simp only [CTree.agreeP, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hs, hn⟩, hr⟩, hw⟩, ht⟩ := h
    subst hn
    have er := reqTree_eval hs hr ρ
    have ew := wsTree_eval hw ρ
    refine ⟨?_, ?_, ?_⟩
    · simp only [CTree.eval, er, ew]
      split
      · exact Tree.eval_of_agree ht _
      · rfl
    · intro r0 ws0 n0 h0
      simp only [CTree.reach, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl, rfl⟩ := h0
      exact ⟨r', ws', rfl, er, ew⟩
    · intro r0 ws0 n0 h0
      simp only [CTree.reach, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl, rfl⟩ := h0
      exact ⟨r, ws, rfl, er.symm, ew.symm⟩
  | .tree _, .ite _ _ _, h, _, _ => by simp [CTree.agreeP] at h
  | .tree _, .call _ _ _ _, h, _, _ => by simp [CTree.agreeP] at h
  | .ite _ _ _, .tree _, h, _, _ => by simp [CTree.agreeP] at h
  | .ite _ _ _, .call _ _ _ _, h, _, _ => by simp [CTree.agreeP] at h
  | .call _ _ _ _, .tree _, h, _, _ => by simp [CTree.agreeP] at h
  | .call _ _ _ _, .ite _ _ _, h, _, _ => by simp [CTree.agreeP] at h

/-- Whether two call trees agree, once prepared. -/
def CTree.agree (T1 T2 : CTree) : Bool := CTree.agreeP T1.prep T2.prep

/-- **Agreeing call trees are equal on every call, for every callee**, and reach requests with the
same values, after writes that leave the same storage. -/
theorem CTree.agree_sound {T1 T2 : CTree} (h : CTree.agree T1 T2 = true) (ρ : Val) (A : Callee) :
    T1.eval ρ A = T2.eval ρ A ∧
      (∀ r ws n, T1.reach ρ = some (r, ws, n) → ∃ r' ws', T2.reach ρ = some (r', ws', n) ∧
        r.eval ρ = r'.eval ρ ∧ Writes.store ρ ws = Writes.store ρ ws') ∧
      (∀ r ws n, T2.reach ρ = some (r, ws, n) → ∃ r' ws', T1.reach ρ = some (r', ws', n) ∧
        r.eval ρ = r'.eval ρ ∧ Writes.store ρ ws = Writes.store ρ ws') := by
  have s := CTree.agreeP_sound h ρ A
  rw [CTree.eval_prep, CTree.eval_prep, CTree.reach_prep, CTree.reach_prep] at s
  exact s

end SolidCore.Refinement.Generic
