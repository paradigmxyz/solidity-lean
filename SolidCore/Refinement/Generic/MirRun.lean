import SolidCore.Refinement.Generic.Mir

/-!
# The symbolic run of lowered MIR is sound

`symTree_sound`: on a call that gives the symbolic run what `CallFacts` says (no value, call
data of `4 + 32 * n` bytes whose words are the arguments and whose selector is `sel`, storage
`ρ.store`, which reads every slot as a word), SolarTV's lowered MIR semantics `moduleSem o` runs
the module, under every oracle `o`, to the result of the tree `symTree` computes; with the
environment flag set, the oracle must be one `EnvOk` describes: its caller is the call's, `ρ.caller`, and its
hash of the 64 bytes of two words is `ρ.hash` of them. `symTreeValue_sound` is the same for a call
with a value other than 0 and the tree `symTreeValue` computes. Both are cases of one run whose
value is a symbolic value `cv` (`CallFactsAt`).

The proof relates each machine word to its symbolic value (`SV.Rel`), the environment pointwise
(`EnvRel`), the returns of the internal calls in progress one by one (`StackRel`) and the
machine state to the symbolic state (`StRel`: memory bytes, storage through the writes, the logs
of its world), and shows each step keeps them: pure operations (`symPure_sound`, on the word
semantics of `EvmRules.Evm`), effects (`symEffect_sound`), instructions (`symInsts_sound`, where
an `assume` holds by the facts of the path, `WExpr.eval_simp`), terminators (`symTerm_sound`), the
rest of a block (`symSegment_sound`) and a step of the module (`symStep_sound`), then the whole
run by induction on the fuel (`symRun_sound`), where a branch on a symbolic word follows the side
the call's words take and that side's facts hold (`Facts.Hold.add`).
-/

namespace SolidCore.Refinement.Generic
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered EvmRules

/-! ## Relations -/

/-- A word holds a symbolic value; `SV.paid` holds every word but 0. -/
def SV.Rel (ρ : Val) (call : Call) (v : Word) : SV → Prop
  | .w e => v.toNat = e.eval ρ
  | .cd0 => v = calldataWord call 0
  | .paid => v ≠ 0

/-- The 32 bytes of a word, big-endian. -/
def wordBytes (v : Nat) : List (BitVec 8) :=
  (List.range 32).map fun i => BitVec.ofNat 8 (v / 256 ^ (31 - i))

/-- An oracle whose environment the symbolic run with the environment flag takes: its caller
is the call's, `ρ.caller` below `2 ^ 160`, and its hash of the 64 bytes of two words is `ρ.hash` of them. -/
structure EnvOk (o : Oracle) (ρ : Val) : Prop where
  caller : (o.caller.setWidth 256).toNat = ρ.caller % 2 ^ 160
  hash : ∀ a b, a < wordSize → b < wordSize →
    (o.keccak (wordBytes a ++ wordBytes b)).toNat = ρ.hash a b % wordSize

/-- What the flags `ev` ask of the oracle: its caller when they read the caller, its hash of two
words when they hash. -/
structure EnvAsk (ev : EnvFlags) (o : Oracle) (ρ : Val) : Prop where
  caller : ev.caller = true → (o.caller.setWidth 256).toNat = ρ.caller % 2 ^ 160
  hash : ev.hash = true → ∀ a b, a < wordSize → b < wordSize →
    (o.keccak (wordBytes a ++ wordBytes b)).toNat = ρ.hash a b % wordSize

/-- An oracle `EnvOk` describes gives every flag what it asks. -/
theorem EnvOk.ask {o : Oracle} {ρ : Val} (h : EnvOk o ρ) (ev : EnvFlags) : EnvAsk ev o ρ :=
  ⟨fun _ => h.caller, fun _ => h.hash⟩

/-- The flags off ask nothing. -/
theorem EnvAsk.off (o : Oracle) (ρ : Val) : EnvAsk .off o ρ :=
  ⟨fun h => by simp [EnvFlags.off] at h, fun h => by simp [EnvFlags.off] at h⟩

/-- What the call gives the symbolic run: no value, `4 + 32 * n` bytes of call data whose word at
`4 + 32 * i` is argument `i` and whose first four bytes are the selector `sel`, and the
storage `ρ.store`, which reads every slot as a word. -/
structure CallFacts (sel n : Nat) (ρ : Val) (call : Call) : Prop where
  value : call.callvalue = 0
  size : call.calldata.size = 4 + 32 * n
  args : ∀ i, i < n → 4 + 32 * i < wordSize →
    (calldataWord call (BitVec.ofNat 256 (4 + 32 * i))).toNat = (WExpr.arg i).eval ρ
  selector : Evm.shr 224 (calldataWord call 0) = BitVec.ofNat 256 sel
  store : ρ.store = slotValue call.storage
  ok : ρ.Ok

/-- What the call gives the symbolic run whose value is `cv`: its value word holds `cv`, and
the rest is `CallFacts`'s. -/
structure CallFactsAt (cv : SV) (sel n : Nat) (ρ : Val) (call : Call) : Prop where
  value : SV.Rel ρ call (BitVec.ofNat 256 call.callvalue) cv
  size : call.calldata.size = 4 + 32 * n
  args : ∀ i, i < n → 4 + 32 * i < wordSize →
    (calldataWord call (BitVec.ofNat 256 (4 + 32 * i))).toNat = (WExpr.arg i).eval ρ
  selector : Evm.shr 224 (calldataWord call 0) = BitVec.ofNat 256 sel
  store : ρ.store = slotValue call.storage
  ok : ρ.Ok

/-- A call with no value gives the run whose value is the word 0 its facts. -/
theorem CallFacts.at {sel n : Nat} {ρ : Val} {call : Call} (hc : CallFacts sel n ρ call) :
    CallFactsAt (.w (.lit 0)) sel n ρ call where
  value := by simp [SV.Rel, WExpr.eval, hc.value]
  size := hc.size
  args := hc.args
  selector := hc.selector
  store := hc.store
  ok := hc.ok

def EnvRel (ρ : Val) (call : Call) (env : Env) (senv : SEnv) : Prop :=
  ∀ j, SV.Rel ρ call (env j) (senv j)

def ArgsRel (ρ : Val) (call : Call) : List Word → List SV → Prop
  | [], [] => True
  | a :: as, s :: ss => SV.Rel ρ call a s ∧ ArgsRel ρ call as ss
  | _, _ => False

def OptRel (ρ : Val) (call : Call) : Option Word → Option SV → Prop
  | none, none => True
  | some v, some s => SV.Rel ρ call v s
  | _, _ => False

/-- A machine state holds a symbolic state: its memory bytes, its storage (the writes over the
storage before the call) and the logs of its world. -/
structure StRel (ρ : Val) (s : State) (st : SState) : Prop where
  mem : ∀ i, (s.memory.bytes i).toNat = (st.mem i).eval ρ
  store : ∀ k : Word, (s.storage k).toNat = Writes.store ρ st.writes k.toNat
  world : logs s = st.logs.map (Log.eval ρ)

/-- The returns of the calls in progress hold the symbolic ones: the same places, the caller's
values related. -/
def StackRel (ρ : Val) (call : Call) : List Return → List SReturn → Prop
  | [], [] => True
  | r :: rs, q :: qs =>
    r.fn = q.fn ∧ r.block = q.block ∧ r.dst = q.dst ∧ r.rest = q.rest ∧ r.term = q.term ∧
      r.extras = [] ∧ r.publish = none ∧ EnvRel ρ call r.env q.env ∧ StackRel ρ call rs qs
  | _, _ => False

theorem eq_ofNat_of_rel {ρ : Val} {call : Call} {v : Word} {n : Nat}
    (h : SV.Rel ρ call v (.w (.lit n))) : v = BitVec.ofNat 256 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [SV.Rel, WExpr.eval] at h
  simp [h]

theorem toNat_of_rel {ρ : Val} {call : Call} {v : Word} {n : Nat}
    (h : SV.Rel ρ call v (.w (.lit n))) : v.toNat = n % wordSize := h

theorem EnvRel.set {ρ : Val} {call : Call} {env : Env} {senv : SEnv} (h : EnvRel ρ call env senv)
    {v : Word} {s : SV} (hv : SV.Rel ρ call v s) (d : Nat) :
    EnvRel ρ call (env.set d v) (senv.set d s) := by
  intro j
  simp only [Env.set, SEnv.set]
  split
  · exact hv
  · exact h j

theorem rel_operand {ρ : Val} {call : Call} {env : Env} {senv : SEnv} (h : EnvRel ρ call env senv)
    (op : Operand) : SV.Rel ρ call (op.eval env) (SV.ofOperand senv op) := by
  cases op with
  | value id => exact h id
  | const word =>
    simp only [Operand.eval, SV.ofOperand, SV.Rel, WExpr.eval]
    exact (Nat.mod_eq_of_lt word.isLt).symm

theorem rel_args {ρ : Val} {call : Call} {env : Env} {senv : SEnv} (h : EnvRel ρ call env senv) :
    ∀ ops : List Operand, ArgsRel ρ call (ops.map (Operand.eval env)) (ops.map (SV.ofOperand senv))
  | [] => trivial
  | op :: ops => ⟨rel_operand h op, rel_args h ops⟩

/-! ## Word operations -/

theorem shl_toNat_eval (a b : Word) :
    (Evm.shl a b).toNat = BinOp.shl.eval a.toNat b.toNat % wordSize := by
  simp only [Evm.shl, BinOp.eval, BitVec.ult]
  have h' : (256 : BitVec 256).toNat = 256 := rfl
  by_cases h : a.toNat < 256
  · simp [h, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · simp [h]

theorem shr_toNat_eval (a b : Word) :
    (Evm.shr a b).toNat = BinOp.shr.eval a.toNat b.toNat % wordSize := by
  simp only [Evm.shr, BinOp.eval, BitVec.ult]
  have h' : (256 : BitVec 256).toNat = 256 := rfl
  by_cases h : a.toNat < 256
  · simp only [h', h, decide_true, Bool.cond_true, ↓reduceIte, BitVec.ushiftRight_eq',
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) b.isLt)).symm
  · simp [h]

theorem byte_toNat_eval (a b : Word) :
    (Evm.byte a b).toNat = BinOp.byte.eval a.toNat b.toNat % wordSize := by
  simp only [Evm.byte, BinOp.eval, BitVec.ult]
  have h' : (32 : BitVec 256).toNat = 32 := rfl
  by_cases h : a.toNat < 32
  · simp only [h', h, decide_true, Bool.cond_true, ↓reduceIte]
    have hmul : (((31 : BitVec 256) - a) * 8).toNat = (31 - a.toNat) * 8 := by
      simp only [BitVec.toNat_mul, BitVec.toNat_sub]
      have h31 : (31 : BitVec 256).toNat = 31 := rfl
      have h8 : (8 : BitVec 256).toNat = 8 := rfl
      simp only [h31, h8]
      omega
    have h255 : (255 : BitVec 256).toNat = 2 ^ 8 - 1 := rfl
    rw [BitVec.toNat_and, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, hmul,
      Nat.shiftRight_eq_div_pow, h255, Nat.and_two_pow_sub_one_eq_mod]
    have hpow : (2 : Nat) ^ ((31 - a.toNat) * 8) = 256 ^ (31 - a.toNat) := by
      rw [Nat.mul_comm, Nat.pow_mul]
    rw [hpow]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm
  · simp [h]

theorem evalPure_bin {op : EVM.Op} {o : BinOp} (h : binOfOp op = some o) (a b : Word) :
    ∃ w, evalPure op [a, b] = some w ∧ w.toNat = o.eval a.toNat b.toNat % wordSize := by
  have ha := a.isLt
  have hb := b.isLt
  cases op <;> simp only [binOfOp, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    refine ⟨_, rfl, ?_⟩
  · simp [Evm.eq, BinOp.eval, BitVec.toNat_eq]; split <;> simp
  · simp [Evm.sub, BinOp.eval, BitVec.toNat_sub, Nat.add_comm]
  · simp [Evm.add, BinOp.eval, BitVec.toNat_add]
  · simp [Evm.mul, BinOp.eval, BitVec.toNat_mul]
  · simp only [Evm.and, BinOp.eval, BitVec.toNat_and]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left ha)).symm
  · simp only [Evm.or, BinOp.eval, BitVec.toNat_or]
    exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)).symm
  · simp only [Evm.xor, BinOp.eval, BitVec.toNat_xor]
    exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)).symm
  · simp only [Evm.div, BinOp.eval, BitVec.toNat_udiv]
    split
    · rename_i h0; simp [h0]
    · exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)).symm
  · simp only [Evm.lt, BinOp.eval, BitVec.ult]
    by_cases h : a.toNat < b.toNat <;> simp [h]
  · simp only [Evm.gt, BinOp.eval, BitVec.ult]
    by_cases h : b.toNat < a.toNat <;> simp [h]
  · exact byte_toNat_eval a b
  · exact shl_toNat_eval a b
  · exact shr_toNat_eval a b

theorem evalPure_iszero (a : Word) :
    evalPure .iszero [a] = some (Evm.iszero a) ∧
      (Evm.iszero a).toNat = UnOp.iszero.eval a.toNat % wordSize := by
  refine ⟨rfl, ?_⟩
  simp only [Evm.iszero, UnOp.eval]
  by_cases h : a = 0
  · subst h; simp
  · have : a.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    have h' : ¬ a = 0#256 := h
    simp [h', this]

theorem evalPure_not (a : Word) :
    evalPure .not [a] = some (Evm.not a) ∧
      (Evm.not a).toNat = UnOp.not.eval a.toNat % wordSize := by
  refine ⟨rfl, ?_⟩
  have ha := a.isLt
  simp only [Evm.not, UnOp.eval, BitVec.toNat_not]
  exact (Nat.mod_eq_of_lt (by simp only [wordSize]; omega)).symm

theorem ne_toNat (a b : Word) :
    (Evm.ne a b).toNat = UnOp.iszero.eval (BinOp.eq.eval a.toNat b.toNat % wordSize) % wordSize := by
  simp only [Evm.ne, UnOp.eval, BinOp.eval]
  by_cases h : a = b
  · subst h; simp
  · have : a.toNat ≠ b.toNat := fun h' => h (BitVec.eq_of_toNat_eq h')
    simp [h, this]

theorem symPure_sound {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call)
    {op : EVM.Op} {args : List Word} {sargs : List SV} {sv : SV}
    (h : symPure sel op sargs = some sv) (hr : ArgsRel ρ call args sargs) :
    ∃ v, evalPure op args = some v ∧ SV.Rel ρ call v sv := by
  unfold symPure at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    match args, hr with
    | [a, c], ⟨ha, hc0, _⟩ =>
      rw [eq_ofNat_of_rel ha]
      simp only [SV.Rel] at hc0
      subst hc0
      refine ⟨Evm.shr 224 (calldataWord call 0), rfl, ?_⟩
      simp only [SV.Rel, hc.selector, WExpr.eval, BitVec.toNat_ofNat]
  · simp only [Option.some.injEq] at h
    subst h
    match args, hr with
    | [x], ⟨hx, _⟩ =>
      obtain ⟨h1, h2⟩ := evalPure_iszero x
      refine ⟨_, h1, ?_⟩
      simp only [SV.Rel] at hx ⊢
      rw [eval_mkUn, h2]
      simp only [WExpr.eval, hx]
  · simp only [Option.some.injEq] at h
    subst h
    match args, hr with
    | [x], ⟨hx, _⟩ =>
      obtain ⟨h1, h2⟩ := evalPure_not x
      refine ⟨_, h1, ?_⟩
      simp only [SV.Rel] at hx ⊢
      rw [eval_mkUn, h2]
      simp only [WExpr.eval, hx]
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    match args, hr with
    | [x, y], ⟨hx, hy, _⟩ =>
      obtain ⟨w, hw, hwv⟩ := evalPure_bin ho x y
      refine ⟨w, hw, ?_⟩
      simp only [SV.Rel] at hx hy ⊢
      rw [eval_mkBin, hwv]
      simp only [WExpr.eval, hx, hy]
  · -- iszero of a value other than 0
    simp only [Option.some.injEq] at h
    subst h
    match args, hr with
    | [x], ⟨hx, _⟩ =>
      obtain ⟨h1, h2⟩ := evalPure_iszero x
      refine ⟨_, h1, ?_⟩
      have hx' : x.toNat ≠ 0 := fun h0 => hx (BitVec.eq_of_toNat_eq (by simpa using h0))
      simp only [SV.Rel, WExpr.eval]
      rw [h2]
      simp [UnOp.eval, hx']
  · -- eq of a value other than 0 and 0
    split at h
    · rename_i hz
      simp only [Option.some.injEq] at h
      subst h
      match args, hr with
      | [x, y], ⟨hx, hy, _⟩ =>
        obtain ⟨w, hw, hwv⟩ := evalPure_bin (op := .eq) (o := .eq) rfl x y
        refine ⟨w, hw, ?_⟩
        have hx' : x.toNat ≠ 0 := fun h0 => hx (BitVec.eq_of_toNat_eq (by simpa using h0))
        simp only [SV.Rel, WExpr.eval, hz] at hy ⊢
        rw [hwv]
        simp [BinOp.eval, hy, hx']
    · simp at h
  · -- eq of 0 and a value other than 0
    split at h
    · rename_i hz
      simp only [Option.some.injEq] at h
      subst h
      match args, hr with
      | [x, y], ⟨hx, hy, _⟩ =>
        obtain ⟨w, hw, hwv⟩ := evalPure_bin (op := .eq) (o := .eq) rfl x y
        refine ⟨w, hw, ?_⟩
        have hy' : y.toNat ≠ 0 := fun h0 => hy (BitVec.eq_of_toNat_eq (by simpa using h0))
        simp only [SV.Rel, WExpr.eval, hz] at hx ⊢
        rw [hwv]
        simp [BinOp.eval, hx, Ne.symm hy']
    · simp at h
  · simp at h


/-! ## Effects -/

theorem byte_toNat (v : Word) (j : Nat) :
    (Memory.byte v j).toNat = v.toNat / 256 ^ (31 - j) % 256 := by
  simp only [Memory.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) ^ (31 - j) = 2 ^ (8 * (31 - j)) by rw [Nat.pow_mul]]


theorem calldataArg_sound {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call)
    {ow : Word} {off : Nat} (how : ow.toNat = off % wordSize) {v : SV}
    (h : calldataArg n (off % wordSize) = some v) : SV.Rel ρ call (calldataWord call ow) v := by
  unfold calldataArg at h
  split at h
  · rename_i h0
    simp only [Option.some.injEq] at h
    subst h
    have : ow = 0 := BitVec.eq_of_toNat_eq (by rw [how, h0]; rfl)
    subst this
    rfl
  · split at h
    · rename_i h0 hi
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h4, hm, hlt⟩ := hi
      have hoff : off % wordSize = 4 + 32 * ((off % wordSize - 4) / 32) := by omega
      have : ow = BitVec.ofNat 256 (4 + 32 * ((off % wordSize - 4) / 32)) := by
        apply BitVec.eq_of_toNat_eq
        rw [how, BitVec.toNat_ofNat, ← hoff, Nat.mod_mod]
      rw [this]
      exact hc.args _ hlt (by rw [← hoff]; exact Nat.mod_lt _ (by decide))
    · simp at h


theorem bytes_expand (m : Mem) (o sz : Nat) : (m.expand o sz).bytes = m.bytes := by
  unfold Mem.expand; split <;> rfl

theorem callerWord_lt : callerWord < wordSize := by decide

/-- Memory bytes that hold the symbolic bytes of one word are its bytes. -/
theorem memWord_bytes {ρ : Val} {bytes : Nat → BitVec 8} {mem : Nat → OByte}
    (hm : ∀ i, (bytes i).toNat = (mem i).eval ρ) {off : Nat} {e : WExpr}
    (h : memWord mem off = some e) :
    ∀ i, i < 32 → bytes (off + i) = BitVec.ofNat 8 (e.eval ρ / 256 ^ (31 - i)) := by
  intro i hi
  unfold memWord at h
  split at h
  · rename_i e' j _
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h
      subst h
      have hi' := List.all_eq_true.mp hall i (List.mem_range.mpr hi)
      simp only [beq_iff_eq] at hi'
      apply BitVec.eq_of_toNat_eq
      rw [hm, hi', BitVec.toNat_ofNat]
      rfl
    · simp at h
  · simp at h

/-- 64 bytes that hold two words are the bytes the oracle hashes for them. -/
theorem read_two_words {bytes : Nat → BitVec 8} {off a b : Nat}
    (ha : ∀ i, i < 32 → bytes (off + i) = BitVec.ofNat 8 (a / 256 ^ (31 - i)))
    (hb : ∀ i, i < 32 → bytes (off + 32 + i) = BitVec.ofNat 8 (b / 256 ^ (31 - i))) :
    (List.range 64).map (fun i => bytes (off + i)) = wordBytes a ++ wordBytes b := by
  rw [show 64 = 32 + 32 from rfl, List.range_add, List.map_append, List.map_map]
  unfold wordBytes
  congr 1
  · exact List.map_congr_left fun i hi => ha i (List.mem_range.mp hi)
  · apply List.map_congr_left
    intro i hi
    simp only [Function.comp, ← Nat.add_assoc]
    exact hb i (List.mem_range.mp hi)

/-- The words of symbolic values that are all words are the machine words' values. -/
theorem svWords_sound {ρ : Val} {call : Call} : ∀ {args : List Word} {sargs : List SV}
    {ts : List WExpr}, svWords sargs = some ts → ArgsRel ρ call args sargs →
    args.length = sargs.length ∧ args.map BitVec.toNat = ts.map (WExpr.eval ρ)
  | [], [], ts, h, _ => by
    simp only [svWords, Option.some.injEq] at h
    subst h
    simp
  | a :: as, .w e :: ss, ts, h, hr => by
    simp only [svWords, Option.map_eq_some_iff] at h
    obtain ⟨ts', h', rfl⟩ := h
    obtain ⟨h1, h2⟩ := svWords_sound h' hr.2
    refine ⟨by simp [h1], ?_⟩
    simp only [List.map_cons, h2, List.cons.injEq, and_true]
    exact hr.1
  | _ :: _, .cd0 :: _, _, h, _ => by simp [svWords] at h
  | _ :: _, .paid :: _, _, h, _ => by simp [svWords] at h
  | [], _ :: _, _, _, hr => by simp [ArgsRel] at hr
  | _ :: _, [], _, _, hr => by simp [ArgsRel] at hr

theorem logs_append_log (s : State) (mem : Mem) (topics : List Word) (data : List Memory.Byte) :
    logs ⟨mem, s.storage, s.transient, s.world ++ [.log topics data]⟩ =
      logs s ++ [(topics.map BitVec.toNat, data.map BitVec.toNat)] := by
  simp [logs, List.filterMap_append]

theorem read_eq {ρ : Val} {s : State} {st : SState} (hs : StRel ρ s st) (m : Mem)
    (hm : m.bytes = s.memory.bytes) (o sz : Nat) :
    (m.read o sz).map BitVec.toNat = (outBytes st.mem o sz).map (OByte.eval ρ) := by
  simp only [Mem.read, outBytes, List.map_map, hm]
  apply List.map_congr_left
  intro i _
  exact hs.mem (o + i)

/-- A state whose memory only grew holds the same symbolic state. -/
theorem StRel.expand {ρ : Val} {s : State} {st : SState} (hs : StRel ρ s st) (o sz : Nat) :
    StRel ρ { s with memory := s.memory.expand o sz } st where
  mem i := by simp only [bytes_expand]; exact hs.mem i
  store := hs.store
  world := hs.world

theorem symEffect_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ)
    {eff : Effect} {args : List Word} {sargs : List SV} {s : State} {st st' : SState}
    {res : Option SV} (h : symEffect ev cv n eff sargs st = some (res, st'))
    (hr : ArgsRel ρ call args sargs) (hs : StRel ρ s st) :
    ∃ res' s', eff.apply o call args s = some (res', s') ∧ OptRel ρ call res' res ∧ StRel ρ s' st' := by
  unfold symEffect at h
  split at h
  · -- calldatasize
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    match args, hr with
    | [], _ =>
      refine ⟨_, _, rfl, ?_, hs⟩
      simp [OptRel, SV.Rel, WExpr.eval, hc.size]
  · -- callvalue
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    match args, hr with
    | [], _ =>
      refine ⟨_, _, rfl, ?_, hs⟩
      exact hc.value
  · -- calldataload
    rename_i off
    obtain ⟨v, hv, h⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    match args, hr with
    | [ow], ⟨how, _⟩ =>
      exact ⟨_, _, rfl, calldataArg_sound hc (toNat_of_rel how) hv, hs⟩
  · -- sload
    rename_i k
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    match args, hr with
    | [kw], ⟨hk, _⟩ =>
      refine ⟨_, _, rfl, ?_, hs⟩
      simp only [OptRel, SV.Rel] at hk ⊢
      rw [hs.store kw, hk, Writes.eval_read hc.ok]
  · -- sstore
    rename_i k e
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    match args, hr with
    | [kw, vw], ⟨hk, hv, _⟩ =>
      refine ⟨_, _, rfl, trivial, ?_⟩
      simp only [SV.Rel] at hk hv
      exact { mem := hs.mem, world := hs.world
              store := fun q => by
                simp only [update, Writes.store_set, Nat.mod_eq_of_lt q.isLt, ← hk]
                by_cases hq : q = kw
                · subst hq; simp [hv]
                · have : ¬ kw.toNat = q.toNat := fun h' => hq (BitVec.eq_of_toNat_eq h'.symm)
                  simp only [hq, this, ite_false]; exact hs.store q }
  · -- mstore
    rename_i off e
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    match args, hr with
    | [ow, vw], ⟨ho, hv, _⟩ =>
      refine ⟨_, _, rfl, trivial, ?_⟩
      have hon := toNat_of_rel ho
      exact { store := hs.store, world := hs.world
              mem := fun i => by
                simp only [Mem.store, bytes_expand, storeBytes, hon]
                by_cases hi : off % wordSize ≤ i ∧ i < off % wordSize + 32
                · simp only [hi, and_self, ite_true, OByte.eval, byte_toNat]
                  simp only [SV.Rel] at hv
                  rw [hv]
                · simp only [hi, ite_false]
                  exact hs.mem i }
  · -- caller
    split at h
    · rename_i hev
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      match args, hr with
      | [], _ =>
        refine ⟨_, _, rfl, ?_, hs⟩
        simp only [OptRel, SV.Rel, WExpr.eval, henv.caller hev]
    · simp at h
  · -- keccak256
    rename_i off size
    split at h
    · rename_i hcond
      obtain ⟨hev, h64⟩ := hcond
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        match args, hr with
        | [ow, sw], ⟨ho, hsz, _⟩ =>
          refine ⟨_, _, rfl, ?_, hs.expand _ _⟩
          have hread : (s.memory.expand ow.toNat sw.toNat).read ow.toNat sw.toNat =
              wordBytes (a.eval ρ) ++ wordBytes (b.eval ρ) := by
            unfold Mem.read
            rw [bytes_expand, toNat_of_rel hsz, h64, toNat_of_rel ho]
            exact read_two_words (memWord_bytes hs.mem ha) (memWord_bytes hs.mem hb)
          simp only [OptRel, SV.Rel, WExpr.eval]
          rw [hread, henv.hash hev _ _ (a.eval_lt ρ) (b.eval_lt ρ)]
      · simp at h
    · simp at h
  · -- log
    rename_i k off size topics
    split at h
    · rename_i hlen
      split at h
      · rename_i ts hts
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        match args, hr with
        | ow :: sw :: mts, ⟨ho, hsz, hts'⟩ =>
          obtain ⟨hl, hmap⟩ := svWords_sound hts hts'
          have happ : Effect.apply o call (.log k) (ow :: sw :: mts) s =
              some (none, ⟨s.memory.expand ow.toNat sw.toNat, s.storage, s.transient,
                s.world ++ [.log mts ((s.memory.expand ow.toNat sw.toNat).read ow.toNat sw.toNat)]⟩) := by
            simp only [Effect.apply, hl, hlen, ite_true]
          refine ⟨_, _, happ, trivial, ?_⟩
          exact { mem := fun i => by simp only [bytes_expand]; exact hs.mem i
                  store := hs.store
                  world := by
                    rw [logs_append_log, hs.world, List.map_append, List.map_cons, List.map_nil,
                      read_eq hs _ (bytes_expand _ _ _), toNat_of_rel ho, toNat_of_rel hsz, hmap]
                    rfl }
      · simp at h
    · simp at h
  · simp at h



/-! ## Blocks -/

theorem symInsts_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ) {K : Facts}
    (hK : K.Hold ρ) : ∀ (insts : List Inst) (senv senv' : SEnv) (st st' : SState),
      symInsts ev cv sel n K insts senv st = some (senv', st') → ∀ env s, EnvRel ρ call env senv →
      StRel ρ s st → ∃ env' s', execInsts o call insts env s = some (env', s') ∧
        EnvRel ρ call env' senv' ∧ StRel ρ s' st'
  | [], senv, senv', st, st', h, env, s, he, hs => by
    simp only [symInsts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨env, s, rfl, he, hs⟩
  | .pure dst op args :: rest, senv, senv', st, st', h, env, s, he, hs => by
    simp only [symInsts] at h
    split at h
    · rename_i v hv
      obtain ⟨w, hw, hwv⟩ := symPure_sound hc hv (rel_args he args)
      obtain ⟨env', s', h1, h2, h3⟩ :=
        symInsts_sound hc henv hK rest _ _ _ _ h _ s (he.set hwv dst) hs
      exact ⟨env', s', by simp only [execInsts, hw]; exact h1, h2, h3⟩
    · simp at h
  | .effect dst eff args :: rest, senv, senv', st, st', h, env, s, he, hs => by
    simp only [symInsts] at h
    split at h
    · rename_i res st1 hv
      obtain ⟨res', s1, h1, hr1, hs1⟩ := symEffect_sound hc henv hv (rel_args he args) hs
      have key : ∀ (env1 : Env) (senv1 : SEnv), EnvRel ρ call env1 senv1 →
          symInsts ev cv sel n K rest senv1 st1 = some (senv', st') → ∃ env' s',
            execInsts o call rest env1 s1 = some (env', s') ∧ EnvRel ρ call env' senv' ∧
              StRel ρ s' st' :=
        fun env1 senv1 he1 h' => symInsts_sound hc henv hK rest _ _ _ _ h' _ s1 he1 hs1
      simp only [execInsts, h1]
      cases dst <;> cases res' <;> cases res <;> simp only [OptRel] at hr1 <;> dsimp only at h ⊢
      all_goals first
        | exact key _ _ he h
        | exact key _ _ (he.set hr1 _) h
    · simp at h
  | .ne dst a b :: rest, senv, senv', st, st', h, env, s, he, hs => by
    simp only [symInsts] at h
    split at h
    · rename_i x y hx hy
      have ha := rel_operand he a
      have hb := rel_operand he b
      rw [hx] at ha
      rw [hy] at hb
      have hv : SV.Rel ρ call (Evm.ne (a.eval env) (b.eval env)) (.w (mkUn .iszero (mkBin .eq x y))) := by
        simp only [SV.Rel] at ha hb ⊢
        rw [eval_mkUn, ne_toNat]
        simp only [WExpr.eval, eval_mkBin, ha, hb]
      obtain ⟨env', s', h1, h2, h3⟩ :=
        symInsts_sound hc henv hK rest _ _ _ _ h _ s (he.set hv dst) hs
      exact ⟨env', s', by simp only [execInsts]; exact h1, h2, h3⟩
    · -- a value other than 0 against 0
      rename_i z hx hy
      split at h
      · rename_i hz
        have ha := rel_operand he a
        have hb := rel_operand he b
        rw [hx] at ha
        rw [hy] at hb
        have ha' : (a.eval env).toNat ≠ 0 := fun h0 =>
          ha (BitVec.eq_of_toNat_eq (by simpa using h0))
        simp only [SV.Rel, WExpr.eval, hz] at hb
        have hv : SV.Rel ρ call (Evm.ne (a.eval env) (b.eval env)) (.w (.lit 1)) := by
          simp only [SV.Rel, WExpr.eval]
          rw [ne_toNat, hb]
          simp [BinOp.eval, UnOp.eval, ha']
        obtain ⟨env', s', h1, h2, h3⟩ :=
          symInsts_sound hc henv hK rest _ _ _ _ h _ s (he.set hv dst) hs
        exact ⟨env', s', by simp only [execInsts]; exact h1, h2, h3⟩
      · simp at h
    · -- 0 against a value other than 0
      rename_i z hx hy
      split at h
      · rename_i hz
        have ha := rel_operand he a
        have hb := rel_operand he b
        rw [hx] at ha
        rw [hy] at hb
        have hb' : (b.eval env).toNat ≠ 0 := fun h0 =>
          hb (BitVec.eq_of_toNat_eq (by simpa using h0))
        simp only [SV.Rel, WExpr.eval, hz] at ha
        have hv : SV.Rel ρ call (Evm.ne (a.eval env) (b.eval env)) (.w (.lit 1)) := by
          simp only [SV.Rel, WExpr.eval]
          rw [ne_toNat, ha]
          simp [BinOp.eval, UnOp.eval, Ne.symm hb']
        obtain ⟨env', s', h1, h2, h3⟩ :=
          symInsts_sound hc henv hK rest _ _ _ _ h _ s (he.set hv dst) hs
        exact ⟨env', s', by simp only [execInsts]; exact h1, h2, h3⟩
      · simp at h
    · simp at h
  | .assume negated op args :: rest, senv, senv', st, st', h, env, s, he, hs => by
    simp only [symInsts] at h
    split at h
    · rename_i e hv
      split at h
      · rename_i v hl
        obtain ⟨w, hw, hwv⟩ := symPure_sound hc hv (rel_args he args)
        have hwn : w.toNat = v % wordSize := by
          have hse := WExpr.eval_simp hK e
          rw [WExpr.eq_of_lit? hl] at hse
          simp only [SV.Rel] at hwv
          rw [hwv, ← hse]
          rfl
        have hz : (w = 0) ↔ (v % wordSize = 0) := by
          constructor
          · intro h0; rw [← hwn, h0]; rfl
          · intro h0; exact BitVec.eq_of_toNat_eq (by rw [hwn, h0]; rfl)
        simp only [execInsts, hw]
        by_cases h0 : v % wordSize = 0
        · have hw0 := hz.mpr h0
          simp only [h0, ite_true] at h
          simp only [hw0, ite_true]
          cases negated <;> simp only [Bool.false_eq_true, ite_false, ite_true, reduceCtorEq] at h ⊢
          exact symInsts_sound hc henv hK rest _ _ _ _ h env s he hs
        · have hw0 : ¬ w = 0 := fun h' => h0 (hz.mp h')
          simp only [h0, ite_false] at h
          simp only [hw0, ite_false]
          cases negated <;> simp only [Bool.false_eq_true, ite_false, ite_true, reduceCtorEq] at h ⊢
          exact symInsts_sound hc henv hK rest _ _ _ _ h env s he hs
      · simp at h
    · simp at h
  | .word .. :: _, _, _, _, _, h, _, _, _, _ => by simp [symInsts] at h
  | .low .. :: _, _, _, _, _, h, _, _, _, _ => by simp [symInsts] at h
  | .select .. :: _, _, _, _, _, h, _, _, _, _ => by simp [symInsts] at h
  | .call .. :: _, _, _, _, _, h, _, _, _, _ => by simp [symInsts] at h
  | .heapFloor .. :: _, _, _, _, _, h, _, _, _, _ => by simp [symInsts] at h
  | .alloc .. :: _, _, _, _, _, h, _, _, _, _ => by simp [symInsts] at h

theorem symPhis_sound {ρ : Val} {call : Call} {envI : Env} {senvI : SEnv}
    (hI : EnvRel ρ call envI senvI) (pred : Nat) :
    ∀ (phis : List (Nat × List (Nat × Operand))) (senv senv' : SEnv) (env : Env),
      symPhis senvI pred phis senv = some senv' → EnvRel ρ call env senv →
      ∃ env', bindPhis envI pred phis env = some env' ∧ EnvRel ρ call env' senv'
  | [], senv, senv', env, h, he => by
    simp only [symPhis, Option.some.injEq] at h
    subst h
    exact ⟨env, rfl, he⟩
  | (dst, arms) :: rest, senv, senv', env, h, he => by
    simp only [symPhis] at h
    split at h
    · rename_i x op hf
      obtain ⟨env', h1, h2⟩ := symPhis_sound hI pred rest _ _ _ h (he.set (rel_operand hI op) dst)
      exact ⟨env', by simp only [bindPhis, hf]; exact h1, h2⟩
    · simp at h

theorem symSwitch_sound {ρ : Val} {call : Call} {env : Env} {senv : SEnv}
    (he : EnvRel ρ call env senv) {key : Word} {kv : Nat} (hk : key.toNat = kv % wordSize)
    (d : Nat) : ∀ (cs : List (Operand × Nat)) (t : Nat), symSwitch senv kv d cs = some t →
      switchTarget env key d cs = t
  | [], t, h => by simp only [symSwitch, Option.some.injEq] at h; subst h; rfl
  | (c, t') :: rest, t, h => by
    simp only [symSwitch] at h
    split at h
    · rename_i v hv
      have hc := rel_operand he c
      rw [hv] at hc
      have hcn := toNat_of_rel hc
      simp only [switchTarget]
      by_cases heq : v % wordSize = kv % wordSize
      · simp only [heq, ite_true, Option.some.injEq] at h
        subst h
        have : c.eval env = key := BitVec.eq_of_toNat_eq (by rw [hcn, hk, heq])
        simp [this]
      · simp only [heq, ite_false] at h
        have : ¬ c.eval env = key := fun h' => heq (by rw [← hcn, ← hk, h'])
        simp only [this, ite_false]
        exact symSwitch_sound he hk d rest t h
    · simp at h

theorem symBindParams_sound {ρ : Val} {call : Call} :
    ∀ (ps : List Nat) (args : List Word) (sargs : List SV) (env : Env) (senv senv' : SEnv),
      symBindParams ps sargs senv = some senv' → ArgsRel ρ call args sargs →
      EnvRel ρ call env senv → ∃ env', bindParams ps args env = some env' ∧ EnvRel ρ call env' senv'
  | [], [], [], env, senv, senv', h, _, he => by
    simp only [symBindParams, Option.some.injEq] at h
    subst h
    exact ⟨env, rfl, he⟩
  | p :: ps, a :: as, s :: ss, env, senv, senv', h, ⟨ha, hr⟩, he => by
    simp only [symBindParams] at h
    obtain ⟨env', h1, h2⟩ := symBindParams_sound ps as ss _ _ _ h hr (he.set ha p)
    exact ⟨env', by simp only [bindParams]; exact h1, h2⟩
  | [], [], _ :: _, _, _, _, h, _, _ => by simp [symBindParams] at h
  | [], _ :: _, _, _, _, _, _, hr, _ => by cases ‹List SV› <;> simp_all [ArgsRel, symBindParams]
  | _ :: _, [], _, _, _, _, h, hr, _ => by cases ‹List SV› <;> simp_all [ArgsRel, symBindParams]
  | _ :: _, _ :: _, [], _, _, _, h, _, _ => by simp [symBindParams] at h


theorem symBindResult_sound {ρ : Val} {call : Call} {env : Env} {senv : SEnv}
    (he : EnvRel ρ call env senv) : ∀ (dst : Option Nat) (args : List Word) (sargs : List SV)
      (senv' : SEnv), symBindResult senv dst sargs = some senv' → ArgsRel ρ call args sargs →
      ∃ env', bindResult env dst args = some env' ∧ EnvRel ρ call env' senv'
  | none, [], [], senv', h, _ => by
    simp only [symBindResult, Option.some.injEq] at h
    subst h
    exact ⟨env, rfl, he⟩
  | some d, [a], [v], senv', h, hr => by
    simp only [symBindResult, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, he.set hr.1 d⟩
  | none, _ :: _, _, _, h, hr => by
    cases ‹List SV› <;> simp_all [ArgsRel, symBindResult]
  | none, [], _ :: _, _, h, hr => by simp [ArgsRel] at hr
  | some _, [], _, _, h, hr => by cases ‹List SV› <;> simp_all [ArgsRel, symBindResult]
  | some _, _ :: _ :: _, sargs, _, h, hr => by
    match sargs, hr with
    | _ :: _ :: _, _ => simp [symBindResult] at h
  | some _, [_], [], _, h, hr => by simp [ArgsRel] at hr
  | some _, [_], _ :: _ :: _, _, h, hr => by simp [ArgsRel] at hr

/-! ## Steps -/

theorem storageOf_eq {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {s : State}
    {st : SState} (hs : StRel ρ s st) : storageOf s = Writes.store ρ st.writes := by
  funext slot
  simp only [storageOf, hs.store, BitVec.toNat_ofNat]
  exact Writes.store_mod ρ hc.ok slot st.writes

theorem iterate_inr {σ : Type} {step : σ → Option ((Halt × State) ⊕ σ)} {x next : σ}
    (h : step x = some (.inr next)) (k : Nat) : iterate step (k + 1) x = iterate step k next := by
  simp [iterate, h]

theorem iterate_inl {σ : Type} {step : σ → Option ((Halt × State) ⊕ σ)} {x : σ} {r : Halt × State}
    (h : step x = some (.inl r)) : iterate step 1 x = some r := by
  simp [iterate, h]

theorem rel_zero_iff {ρ : Val} {call : Call} {v : Word} {e : WExpr} (h : SV.Rel ρ call v (.w e)) :
    v = 0 ↔ e.eval ρ = 0 := by
  simp only [SV.Rel] at h
  constructor
  · intro h0; rw [← h, h0]; rfl
  · intro h0; exact BitVec.eq_of_toNat_eq (by rw [h, h0]; rfl)

theorem symCallee_some {m : Module} {callee : Nat} {g : Function} (h : symCallee m callee = some g) :
    m.functions[callee]? = some g ∧ ∀ s, g.start s = s := by
  unfold symCallee at h
  split at h
  · rename_i g' hg
    split at h
    · rename_i hn
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hg, fun s => ?_⟩
      unfold Function.start
      cases he : g'.entryHeap with
      | none => rfl
      | some _ => simp [he] at hn
    · simp at h
  · simp at h

theorem entryFree_start {m : Module} (h : entryFree m = true) (s : State) : m.startState s = s := by
  unfold entryFree at h
  unfold Module.startState
  split
  · rename_i f hf
    simp only [hf] at h
    unfold Function.start
    cases he : f.entryHeap with
    | none => rfl
    | some _ => simp [he] at h
  · rfl

/-- What a machine step gives, held by what a symbolic step gives: the same end, or the next
frame related, or for a branch on a word the side the call's words take. -/
def NextOk (ρ : Val) (call : Call) (x : Option ((Halt × State) ⊕ Frame)) : SNext → Prop
  | .done T => ∃ r, x = some (.inl r) ∧ observe call r.2 r.1 = (T.eval ρ).obs
  | .go stack pos senv st => ∃ ms env s, x = some (.inr (ms, pos, env, s)) ∧
      StackRel ρ call ms stack ∧ EnvRel ρ call env senv ∧ StRel ρ s st
  | .fork e stack fn b yes no senv st => ∃ ms env s,
      x = some (.inr (ms, .enter fn b (if e.eval ρ = 0 then no else yes), env, s)) ∧
      StackRel ρ call ms stack ∧ EnvRel ρ call env senv ∧ StRel ρ s st

theorem symTerm_sound {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) (o : Oracle) (m : Module) {stack : List SReturn}
    {fn b : Nat} {senv : SEnv} {st : SState} {term : Terminator} {r : SNext}
    (h : symTerm m stack fn b senv st term = some r) {ms : List Return} {env : Env} {s : State}
    (hst : StackRel ρ call ms stack) (he : EnvRel ρ call env senv) (hs : StRel ρ s st) :
    NextOk ρ call (segment o call m ms fn b [] term env s) r := by
  cases term with
  | jump t =>
    simp only [symTerm, Option.some.injEq] at h
    subst h
    exact ⟨ms, env, s, rfl, hst, he, hs⟩
  | branch c yes no =>
    simp only [symTerm] at h
    have hcr := rel_operand he c
    have hseg : segment o call m ms fn b [] (.branch c yes no) env s =
        some (.inr (ms, .enter fn b (if c.eval env = 0 then no else yes), env, s)) := rfl
    rw [hseg]
    cases hsv : SV.ofOperand senv c with
    | cd0 => simp [hsv] at h
    | paid =>
      simp only [hsv, Option.some.injEq] at h
      subst h
      rw [hsv] at hcr
      have hc0 : ¬ c.eval env = 0 := hcr
      exact ⟨ms, env, s, by simp only [hc0, ↓reduceIte], hst, he, hs⟩
    | w e =>
      simp only [hsv] at h
      rw [hsv] at hcr
      have hz := rel_zero_iff hcr
      cases hl : e.lit? with
      | some v =>
        simp only [hl, Option.some.injEq] at h
        subst h
        have hev : e.eval ρ = v % wordSize := by rw [WExpr.eq_of_lit? hl]; rfl
        refine ⟨ms, env, s, ?_, hst, he, hs⟩
        by_cases h0 : v % wordSize = 0
        · have hc0 : c.eval env = 0 := hz.mpr (by rw [hev, h0])
          simp only [hc0, h0, ↓reduceIte]
        · have hc0 : ¬ c.eval env = 0 := fun h' => h0 (by rw [← hev]; exact hz.mp h')
          simp only [hc0, h0, ↓reduceIte]
      | none =>
        simp only [hl, Option.some.injEq] at h
        subst h
        refine ⟨ms, env, s, ?_, hst, he, hs⟩
        by_cases h0 : e.eval ρ = 0
        · have hc0 : c.eval env = 0 := hz.mpr h0
          simp only [hc0, h0, ↓reduceIte]
        · have hc0 : ¬ c.eval env = 0 := fun h' => h0 (hz.mp h')
          simp only [hc0, h0, ↓reduceIte]
  | switch key d cs =>
    simp only [symTerm] at h
    split at h
    · rename_i kv hkv
      cases hs' : symSwitch senv kv d cs with
      | none => simp [hs'] at h
      | some t =>
        simp only [hs', Option.some.injEq] at h
        subst h
        have hk := rel_operand he key
        rw [hkv] at hk
        have htg := symSwitch_sound he (toNat_of_rel hk) d cs t hs'
        exact ⟨ms, env, s, by simp [segment, splitCall, execInsts, htg], hst, he, hs⟩
    · simp at h
  | tailCall callee args =>
    simp only [symTerm] at h
    cases hg : symCallee m callee with
    | none => simp [hg] at h
    | some g =>
      simp only [hg] at h
      obtain ⟨hg', hstart⟩ := symCallee_some hg
      cases hbp : symBindParams g.params (args.map (SV.ofOperand senv)) (fun _ => .w (.lit 0)) with
      | none => simp [hbp] at h
      | some senv3 =>
        simp only [hbp, Option.some.injEq] at h
        subst h
        have hz : EnvRel ρ call (fun _ => 0) (fun _ => .w (.lit 0)) := fun _ => by
          simp [SV.Rel, WExpr.eval]
        obtain ⟨env3, hbp', he3⟩ := symBindParams_sound g.params _ _ _ _ _ hbp (rel_args he args) hz
        exact ⟨ms, env3, s, by simp only [segment, splitCall, execInsts, hg', hbp', hstart], hst, he3,
          hs⟩
  | leave values =>
    simp only [symTerm] at h
    cases stack with
    | nil => simp at h
    | cons q qs =>
      match ms, hst with
      | r :: rs, ⟨hfn, hb, hdst, hrest, hterm, hextras, hpublish, henvr, hst'⟩ =>
        simp only at h
        cases hbr : symBindResult q.env q.dst (values.map (SV.ofOperand senv)) with
        | none => simp [hbr] at h
        | some env' =>
          simp only [hbr, Option.some.injEq] at h
          subst h
          rw [← hdst] at hbr
          obtain ⟨env'', hbr', he''⟩ :=
            symBindResult_sound henvr r.dst _ _ _ hbr (rel_args he values)
          have hbr2 : bindResults r.env r.dst r.extras (values.map (Operand.eval env)) = some env'' := by
            rw [hextras]; exact hbr'
          exact ⟨rs, env'', s, by
              simp [segment, splitCall, execInsts, hbr2, hfn, hb, hrest, hterm, hpublish,
                publishResults],
            hst', he'', hs⟩
  | ret off size =>
    simp only [symTerm] at h
    split at h
    · rename_i ov sv hov hsv
      simp only [Option.some.injEq] at h
      subst h
      have h1 := rel_operand he off
      have h2 := rel_operand he size
      rw [hov] at h1
      rw [hsv] at h2
      refine ⟨_, rfl, ?_⟩
      simp only [halt, observe, Tree.eval, Res.obs, Bool.false_eq_true, ↓reduceIte,
        toNat_of_rel h1, toNat_of_rel h2]
      congr 1
      · exact read_eq hs _ (bytes_expand _ _ _) _ _
      · exact hs.world
      · exact storageOf_eq hc (s := s) hs
    · simp at h
  | revert off size =>
    simp only [symTerm] at h
    split at h
    · rename_i ov sv hov hsv
      simp only [Option.some.injEq] at h
      subst h
      have h1 := rel_operand he off
      have h2 := rel_operand he size
      rw [hov] at h1
      rw [hsv] at h2
      refine ⟨_, rfl, ?_⟩
      simp only [halt, observe, Tree.eval, Res.obs, ↓reduceIte, toNat_of_rel h1, toNat_of_rel h2,
        hc.store, Bool.false_eq_true]
      congr 1
      exact read_eq hs _ (bytes_expand _ _ _) _ _
    · simp at h
  | stop =>
    simp only [symTerm, Option.some.injEq] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    simp only [observe, Tree.eval, Res.obs, ite_true, hs.world, storageOf_eq hc hs, List.map_nil]
  | invalid =>
    simp only [symTerm, Option.some.injEq] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    simp only [observe, Tree.eval, Res.obs, hc.store, Bool.false_eq_true, ite_false, List.map_nil]

theorem symSegment_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ) (m : Module)
    {K : Facts} (hK : K.Hold ρ) {stack : List SReturn} {fn b : Nat} {insts : List Inst}
    {term : Terminator} {senv : SEnv} {st : SState} {r : SNext}
    (h : symSegment ev cv m sel n K stack fn b insts term senv st = some r) {ms : List Return}
    {env : Env} {s : State} (hst : StackRel ρ call ms stack) (he : EnvRel ρ call env senv)
    (hs : StRel ρ s st) : NextOk ρ call (segment o call m ms fn b insts term env s) r := by
  unfold symSegment at h
  cases hsp : splitCall insts with
  | mk before next =>
  rw [hsp] at h
  cases next with
  | some c =>
    obtain ⟨dst, callee, args, extras, publish, rest⟩ := c
    cases extras with
    | cons _ _ => simp at h
    | nil =>
    cases publish with
    | some _ => simp at h
    | none =>
    simp only at h
    cases hi : symInsts ev cv sel n K before senv st with
    | none => simp [hi] at h
    | some p =>
      obtain ⟨senv2, st2⟩ := p
      simp only [hi] at h
      obtain ⟨env2, s2, hexec, he2, hs2⟩ := symInsts_sound hc henv hK before _ _ _ _ hi env s he hs
      cases hg : symCallee m callee with
      | none => simp [hg] at h
      | some g =>
        simp only [hg] at h
        obtain ⟨hg', hstart⟩ := symCallee_some hg
        cases hbp : symBindParams g.params (args.map (SV.ofOperand senv2)) (fun _ => .w (.lit 0)) with
        | none => simp [hbp] at h
        | some inner =>
          simp only [hbp, Option.some.injEq] at h
          subst h
          have hz : EnvRel ρ call (fun _ => 0) (fun _ => .w (.lit 0)) := fun _ => by
            simp [SV.Rel, WExpr.eval]
          obtain ⟨env3, hbp', he3⟩ :=
            symBindParams_sound g.params _ _ _ _ _ hbp (rel_args he2 args) hz
          exact ⟨⟨fn, b, dst, rest, term, env2, [], none⟩ :: ms, env3, s2,
            by simp only [segment, hsp, hexec, hg', hbp', hstart],
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, he2, hst⟩, he3, hs2⟩
  | none =>
    simp only at h
    cases hi : symInsts ev cv sel n K before senv st with
    | none => simp [hi] at h
    | some p =>
      obtain ⟨senv2, st2⟩ := p
      simp only [hi] at h
      obtain ⟨env2, s2, hexec, he2, hs2⟩ := symInsts_sound hc henv hK before _ _ _ _ hi env s he hs
      have hseg : segment o call m ms fn b insts term env s = segment o call m ms fn b [] term env2 s2 := by
        simp only [segment, hsp, hexec, splitCall, execInsts]
      rw [hseg]
      exact symTerm_sound hc o m h hst he2 hs2

theorem symStep_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) {o : Oracle} (henv : EnvAsk ev o ρ) (m : Module)
    {K : Facts} (hK : K.Hold ρ) {stack : List SReturn} {pos : Pos} {senv : SEnv} {st : SState}
    {r : SNext} (h : symStep ev cv m sel n K stack pos senv st = some r) {ms : List Return}
    {env : Env} {s : State} (hst : StackRel ρ call ms stack) (he : EnvRel ρ call env senv)
    (hs : StRel ρ s st) : NextOk ρ call (moduleBlock o call m (ms, pos, env, s)) r := by
  cases pos with
  | enter fn pred b =>
    simp only [symStep] at h
    simp only [moduleBlock]
    cases hf : m.functions[fn]? with
    | none => simp [hf] at h
    | some f =>
      simp only [hf] at h ⊢
      cases hb : f.blocks[b]? with
      | none => simp [hb] at h
      | some blk =>
        simp only [hb] at h ⊢
        cases hp : symPhis senv pred blk.phis senv with
        | none => simp [hp] at h
        | some senv1 =>
          simp only [hp] at h
          obtain ⟨env1, hbind, he1⟩ := symPhis_sound he pred blk.phis senv senv1 env hp he
          simp only [hbind]
          exact symSegment_sound hc henv m hK h hst he1 hs
  | resume fn b insts term => exact symSegment_sound hc henv m hK h hst he hs

/-- **The symbolic run is sound**: a tree the symbolic run of a module computes from a frame is
the end the module's run reaches from any frame that holds it, on a path whose facts hold,
under every oracle the environment flag allows. -/
theorem symRun_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) (o : Oracle) (henv : EnvAsk ev o ρ) (m : Module) :
    ∀ (fuel : Nat) (stack : List SReturn) (pos : Pos) (senv : SEnv) (st : SState) (K : Facts)
      (T : Tree), symRun ev cv m sel n fuel stack pos senv st K = some T →
      ∀ ms env s, StackRel ρ call ms stack → EnvRel ρ call env senv → StRel ρ s st → K.Hold ρ →
      ∃ k r, iterate (moduleBlock o call m) k (ms, pos, env, s) = some r ∧
        observe call r.2 r.1 = (T.eval ρ).obs
  | 0, _, _, _, _, _, _, h, _, _, _, _, _, _, _ => by simp [symRun] at h
  | fuel + 1, stack, pos, senv, st, K, T, h, ms, env, s, hst, he, hs, hK => by
    simp only [symRun] at h
    cases hx : symStep ev cv m sel n K stack pos senv st with
    | none => simp [hx] at h
    | some x =>
      have hn := symStep_sound hc henv m hK hx hst he hs
      simp only [hx] at h
      cases x with
      | done T' =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨r, hr, hobs⟩ := hn
        exact ⟨1, r, iterate_inl hr, hobs⟩
      | go stack' pos' senv' st' =>
        obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
        obtain ⟨k, r, hk, hobs⟩ :=
          symRun_sound hc o henv m fuel stack' pos' senv' st' K T h ms' env' s' hst' he' hs' hK
        exact ⟨k + 1, r, by rw [iterate_inr hr]; exact hk, hobs⟩
      | fork e stack' fn b yes no senv' st' =>
        obtain ⟨ms', env', s', hr, hst', he', hs'⟩ := hn
        cases ht : symRun ev cv m sel n fuel stack' (.enter fn b yes) senv' st' (K.add e true) with
        | none => simp [ht] at h
        | some t =>
          cases hf : symRun ev cv m sel n fuel stack' (.enter fn b no) senv' st' (K.add e false) with
          | none => simp [ht, hf] at h
          | some f =>
            simp only [ht, hf, Option.some.injEq] at h
            subst h
            by_cases h0 : e.eval ρ = 0
            · simp only [h0, ite_true] at hr
              obtain ⟨k, r, hk, hobs⟩ := symRun_sound hc o henv m fuel stack' _ senv' st' _ f hf
                ms' env' s' hst' he' hs' (hK.add e false (by simp [h0]))
              refine ⟨k + 1, r, by rw [iterate_inr hr]; exact hk, ?_⟩
              simp only [Tree.eval, h0, ite_true]
              exact hobs
            · simp only [h0, ite_false] at hr
              obtain ⟨k, r, hk, hobs⟩ := symRun_sound hc o henv m fuel stack' _ senv' st' _ t ht
                ms' env' s' hst' he' hs' (hK.add e true (by simp [h0]))
              refine ⟨k + 1, r, by rw [iterate_inr hr]; exact hk, ?_⟩
              simp only [Tree.eval, h0, ite_false]
              exact hobs

theorem StRel.initial {ρ : Val} (call : Call) (h : ρ.store = slotValue call.storage) (hok : ρ.Ok) :
    StRel ρ (State.initial call) SState.initial where
  mem _ := rfl
  store k := by
    have := hok k.toNat
    rw [Nat.mod_eq_of_lt k.isLt] at this
    simp only [State.initial, SState.initial, Writes.store, BitVec.toNat_ofNat, ← h]
    exact this
  world := rfl

/-- The run from the module's entry, whose value is `cv`, is sound on a call that gives it what
`CallFactsAt` says. -/
theorem symRun_entry_sound {ev : EnvFlags} {cv : SV} {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt cv sel n ρ call) (o : Oracle) (henv : EnvAsk ev o ρ) (m : Module)
    {fuel : Nat} {T : Tree} (hfree : entryFree m = true)
    (h : symRun ev cv m sel n fuel [] (.enter m.entry 0 0) (fun _ => .w (.lit 0)) SState.initial [] =
      some T) :
    (moduleSem o).run m call = some (T.eval ρ).obs := by
  have hz : EnvRel ρ call (fun _ => 0) (fun _ => .w (.lit 0)) := fun _ => by
    simp [SV.Rel, WExpr.eval]
  obtain ⟨k, r, hk, hr⟩ := symRun_sound hc o henv m fuel _ _ _ _ _ T h [] _ _ trivial hz
    (StRel.initial call hc.store hc.ok) (fun _ hp => absurd hp List.not_mem_nil)
  rw [← entryFree_start hfree (State.initial call)] at hk
  have e : moduleLayer.result o m call = some r := moduleLayer.result_of_ends ⟨k, hk⟩
  show (moduleLayer.result o m call).map _ = _
  rw [e, ← hr]
  rfl

/-- **SolarTV's lowered MIR runs a module as its symbolic tree**: on a call that gives the
symbolic run what `CallFacts` says, under every oracle (one `EnvOk` describes when the environment
flag is set), the fuel-free semantics shows the tree's result. -/
theorem symTree_sound {sel n : Nat} {ρ : Val} {call : Call} (hc : CallFacts sel n ρ call)
    (o : Oracle) (m : Module) {fuel : Nat} {env : EnvFlags} (henv : EnvAsk env o ρ) {T : Tree}
    (h : symTree m sel n fuel env = some T) :
    (moduleSem o).run m call = some (T.eval ρ).obs := by
  unfold symTree at h
  split at h
  · exact symRun_entry_sound hc.at o henv m ‹_› h
  · simp at h

/-- **SolarTV's lowered MIR runs a module as its symbolic tree with a value**: on a call with a
value other than 0 that gives the symbolic run the rest of what `CallFacts` says, under every
oracle (one that gives the flags what `EnvAsk` says they ask), the fuel-free semantics shows the
result of the tree `symTreeValue` computes. -/
theorem symTreeValue_sound {sel n : Nat} {ρ : Val} {call : Call}
    (hc : CallFactsAt .paid sel n ρ call) (o : Oracle) (m : Module) {fuel : Nat} {env : EnvFlags}
    (henv : EnvAsk env o ρ) {T : Tree} (h : symTreeValue m sel n fuel env = some T) :
    (moduleSem o).run m call = some (T.eval ρ).obs := by
  unfold symTreeValue at h
  split at h
  · exact symRun_entry_sound hc o henv m ‹_› h
  · simp at h

end SolidCore.Refinement.Generic



