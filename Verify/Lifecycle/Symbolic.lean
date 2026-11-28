import Verify.Lifecycle.CreationFrame
import Verify.Lifecycle.Route

/-!
# The creation frame over every argument word at once

`Creation.check` evaluates solar's init code on one list of concrete argument words, so each of
its theorems is about one creation. This module runs the same evaluator symbolically: the
argument words are variables (`E.arg j`), the words the init code computes from them are
expressions over the frame's own word functions (`binOf`, `unOf`), and the memory is a list of
symbolic bytes. Offsets, sizes, jump destinations and storage keys must be concrete; a JUMPI on a
word that depends on the arguments falls through and records that word as a path condition
(`= 0`), which the theorem then assumes.

`symRun_sound` proves once, for every init code, that the symbolic run is the concrete `run` of
the creation code `initArgs init ws` for every argument list `ws` of its length that meets the
path conditions. `deploys_all` turns one kernel evaluation of the Boolean `symCheck` into
`Deploys` for all such argument lists, with the runtime code and the storage given as symbolic
specifications (`codeOf`, `storeOf`); `codeOf_patched` reads a runtime code with immutables
patched from argument words as `patchWord` on solar's runtime code.

Outside: everything `run` refuses, and in addition a symbolic offset, size, jump destination or
storage key, an MLOAD of bytes that are neither all concrete nor one word, a code read of the
argument region by PUSH, and a JUMPI taken on a symbolic condition.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm GasCosts
open SolidCore.Refinement SolidCore.Refinement.Evm

namespace Verify.Lifecycle.Creation.Sym

/-! ## Symbolic words and bytes -/

/-- A word of the creation as a function of the argument words. -/
inductive E where
  | c (v : U256)
  | arg (j : Nat)
  | bin (op : Op) (x y : E)
  | un (op : Op) (x : E)
  deriving DecidableEq, Repr

/-- The word `e` names for the argument words `as`. -/
def E.eval (as : List U256) : E → U256
  | .c v => v
  | .arg j => as.getD j 0
  | .bin op x y =>
    match binOf op with
    | some (_, f) => f (x.eval as) (y.eval as)
    | none => 0
  | .un op x =>
    match unOf op with
    | some (_, f) => f (x.eval as)
    | none => 0

/-- A byte of the creation: concrete, or the byte `i` of a word, most significant first. -/
inductive B where
  | c (b : UInt8)
  | part (e : E) (i : Nat)
  deriving DecidableEq, Repr

def B.eval (as : List U256) : B → UInt8
  | .c b => b
  | .part e i => byteAt (wordBytes (e.eval as)) i

/-- The bytes of a list, as a byte array. -/
def ba (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- The bytes `bs` name for the argument words `as`. -/
def bytesOf (as : List U256) (bs : List B) : ByteArray := ba (bs.map (B.eval as))

/-- The 32 bytes of a symbolic word. -/
def wbytes : E → List B
  | .c w => (wordBytes w).data.toList.map B.c
  | e => (List.range 32).map (B.part e)

/-- The concrete bytes of a list, if every byte is concrete. -/
def consts : List B → Option (List UInt8)
  | [] => some []
  | .c b :: r => (consts r).map (b :: ·)
  | _ :: _ => none

/-- A symbolic MLOAD of 32 bytes: concrete bytes read as their word, the 32 bytes of one word
as that word. -/
def load (bs : List B) : Option E :=
  match consts bs with
  | some cs => some (.c (loadWord (ba cs) 0 32))
  | none =>
    match bs with
    | .part e _ :: _ => if bs = (List.range 32).map (B.part e) then some e else none
    | _ => none

/-- A two-operand opcode on symbolic words, folded when both are concrete. -/
def mkBin (op : Op) (f : U256 → U256 → U256) : E → E → E
  | .c a, .c b => .c (f a b)
  | x, y => .bin op x y

def mkUn (op : Op) (f : U256 → U256) : E → E
  | .c a => .c (f a)
  | x => .un op x

/-! ## Lists for the memory -/

section Lists
variable {α β : Type}

def lExt (l : List α) (z : α) (k : Nat) : List α := l ++ List.replicate k z

def lWrite (l : List α) (s : Nat) (v : List α) : List α :=
  if v.length = 0 then l else l.extract 0 s ++ v ++ l.extract (s + v.length) l.length

def lRead (l : List α) (s k : Nat) : List α :=
  if k = 0 then [] else l.extract s (s + k)

theorem map_lExt (f : α → β) (l : List α) (z : α) (k : Nat) :
    (lExt l z k).map f = lExt (l.map f) (f z) k := by
  simp [lExt, List.map_replicate]

theorem map_lWrite (f : α → β) (l : List α) (s : Nat) (v : List α) :
    (lWrite l s v).map f = lWrite (l.map f) s (v.map f) := by
  unfold lWrite
  simp only [List.length_map]
  split
  · rfl
  · simp [List.map_drop, List.map_take]

theorem map_lRead (f : α → β) (l : List α) (s k : Nat) :
    (lRead l s k).map f = lRead (l.map f) s k := by
  unfold lRead
  split
  · rfl
  · simp [List.map_drop, List.map_take]

end Lists

theorem ba_size (l : List UInt8) : (ba l).size = l.length := by
  simp [ba, ByteArray.size]

theorem ba_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b
  simp only at h
  congr
  exact Array.toList_inj.mp h

theorem ba_data (l : List UInt8) : (ba l).data.toList = l := rfl

theorem memoryExtend_ba (l : List UInt8) (k : Nat) :
    memoryExtend (ba l) k = ba (lExt l 0 k) := by
  apply ba_ext
  simp [memoryExtend, ba, lExt, ByteArray.data_append]

theorem memoryWrite_ba (l v : List UInt8) (s : Nat) :
    memoryWrite (ba l) s (ba v) = ba (lWrite l s v) := by
  unfold memoryWrite lWrite
  rw [ba_size, ba_size]
  split
  · rfl
  · apply ba_ext
    simp [ba, ByteArray.data_append, ByteArray.data_extract, ByteArray.size]

theorem memoryReadBytes_ba (l : List UInt8) (s k : Nat) :
    memoryReadBytes (ba l) s k = ba (lRead l s k) := by
  unfold memoryReadBytes lRead
  split
  · rfl
  · apply ba_ext
    simp [ba, ByteArray.data_extract]

/-! ## Symbolic bytes read back -/

theorem consts_eval {as : List U256} : ∀ {bs : List B} {cs : List UInt8},
    consts bs = some cs → bs.map (B.eval as) = cs
  | [], cs, h => by simp [consts] at h; simp [h]
  | .c b :: r, cs, h => by
    simp only [consts, Option.map_eq_some_iff] at h
    obtain ⟨cs', h', rfl⟩ := h
    simp [B.eval, consts_eval h']
  | .part _ _ :: _, _, h => by simp [consts] at h

theorem size_wordBytes' (w : U256) : (wordBytes w).size = 32 := size_wordBytes w

theorem range_byteAt_wordBytes (w : U256) :
    (List.range 32).map (fun i => byteAt (wordBytes w) i) = (wordBytes w).data.toList := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, Array.length_toList]
    exact (size_wordBytes' w).symm
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, byteAt]
    have : i < (wordBytes w).size := by
      simp only [List.length_map, List.length_range] at h1; rw [size_wordBytes']; exact h1
    rw [dif_pos this] <;> rfl

theorem wbytes_eval (as : List U256) (e : E) :
    bytesOf as (wbytes e) = wordBytes (e.eval as) := by
  unfold bytesOf
  apply ba_ext
  rw [ba_data]
  cases e with
  | c w => simp [wbytes, B.eval, E.eval, List.map_map, Function.comp_def]
  | arg j => simp only [wbytes, List.map_map, Function.comp_def, B.eval]; exact range_byteAt_wordBytes _
  | bin op x y => simp only [wbytes, List.map_map, Function.comp_def, B.eval]; exact range_byteAt_wordBytes _
  | un op x => simp only [wbytes, List.map_map, Function.comp_def, B.eval]; exact range_byteAt_wordBytes _

theorem loadWord_ba_wordBytes (w : U256) : loadWord (ba (wordBytes w).data.toList) 0 32 = w := by
  have : ba (wordBytes w).data.toList = wordBytes w := ba_ext rfl
  rw [this]; exact loadWord_wordBytes w

theorem load_eval {as : List U256} {bs : List B} {e : E} (h : load bs = some e) :
    loadWord (bytesOf as bs) 0 32 = e.eval as := by
  unfold load at h
  split at h
  · rename_i cs hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [bytesOf, consts_eval hc, E.eval]
  · split at h
    · rename_i e' _ _
      split at h
      · rename_i hb
        simp only [Option.some.injEq] at h
        subst h
        rw [hb, bytesOf, List.map_map]
        have hp : ∀ x : E, (B.eval as ∘ B.part x) = fun i => byteAt (wordBytes (x.eval as)) i :=
          fun _ => rfl
        rw [hp, range_byteAt_wordBytes, loadWord_ba_wordBytes]
      · simp at h
    · simp at h

theorem mkBin_eval {as : List U256} {op : Op} {k : Nat} {f : U256 → U256 → U256}
    (h : binOf op = some (k, f)) (x y : E) : (mkBin op f x y).eval as = f (x.eval as) (y.eval as) := by
  unfold mkBin
  split <;> simp [E.eval, h]

theorem mkUn_eval {as : List U256} {op : Op} {k : Nat} {f : U256 → U256}
    (h : unOf op = some (k, f)) (x : E) : (mkUn op f x).eval as = f (x.eval as) := by
  unfold mkUn
  split <;> simp [E.eval, h]

/-! ## The creation code with symbolic argument words -/

/-- The creation code of `init` with the argument words `as`. -/
def codeOfArgs (init : ByteArray) (as : List U256) : ByteArray :=
  initArgs init (as.map BitVec.toNat)

theorem argBytes_cons (a : U256) (as : List U256) :
    argBytes ((a :: as).map BitVec.toNat) = wordBytes a ++ argBytes (as.map BitVec.toNat) := by
  apply ba_ext
  simp [argBytes, wordBytes, ByteArray.data_append, U256.toBeBytes]

theorem argBytes_size' (as : List U256) : (argBytes (as.map BitVec.toNat)).size = 32 * as.length := by
  rw [argBytes_size, List.length_map]

theorem byteAt_argBytes : ∀ (as : List U256) (q : Nat), q < 32 * as.length →
    byteAt (argBytes (as.map BitVec.toNat)) q = byteAt (wordBytes (as.getD (q / 32) 0)) (q % 32)
  | [], q, h => by simp at h
  | a :: as, q, h => by
    rw [argBytes_cons, byteAt_append, size_wordBytes']
    by_cases hq : q < 32
    · rw [if_pos hq, Nat.div_eq_of_lt hq, Nat.mod_eq_of_lt hq]; rfl
    · rw [if_neg hq]
      simp only [List.length_cons] at h
      rw [byteAt_argBytes as (q - 32) (by omega)]
      have h1 : q / 32 = (q - 32) / 32 + 1 := by omega
      have h2 : q % 32 = (q - 32) % 32 := by omega
      rw [h1, h2] <;> rfl

theorem codeOfArgs_size (init : ByteArray) (as : List U256) :
    (codeOfArgs init as).size = init.size + 32 * as.length := by
  rw [codeOfArgs, initArgs, ByteArray.size_append, argBytes_size']

/-- The symbolic byte of the creation code at `p`: the init code's, an argument word's, or zero
past the end. -/
def codeByte (init : ByteArray) (n p : Nat) : B :=
  if p < init.size then .c (byteAt init p)
  else if p - init.size < 32 * n then .part (.arg ((p - init.size) / 32)) ((p - init.size) % 32)
  else .c 0

theorem codeByte_eval {init : ByteArray} {as : List U256} (p : Nat) :
    (codeByte init as.length p).eval as = byteAt (codeOfArgs init as) p := by
  unfold codeByte codeOfArgs initArgs
  rw [byteAt_append]
  split
  · rfl
  · split
    · rename_i _ h
      rw [byteAt_argBytes as _ h]; rfl
    · rename_i _ h
      unfold byteAt
      rw [dif_neg (by rw [argBytes_size']; omega)] <;> rfl

theorem bufferRead_codeOfArgs {init : ByteArray} {as : List U256} (off size : Nat) :
    ((List.range size).map fun i => codeByte init as.length (off + i)).map (B.eval as) =
      bufferRead (codeOfArgs init as) off size := by
  simp only [List.map_map, bufferRead]
  apply List.map_congr_left
  intro i _
  exact codeByte_eval _

theorem byteAt_codeOfArgs_lt {init : ByteArray} {as : List U256} {p : Nat} (h : p < init.size) :
    byteAt (codeOfArgs init as) p = byteAt init p := by
  rw [codeOfArgs, initArgs, byteAt_append, if_pos h]

theorem getElem_codeOfArgs {init : ByteArray} {as : List U256} {p : Nat} (h : p < init.size)
    (h' : p < (codeOfArgs init as).size) : (codeOfArgs init as)[p] = init[p] := by
  have e := byteAt_codeOfArgs_lt (as := as) h
  unfold byteAt at e
  rw [dif_pos h', dif_pos h] at e
  exact e

theorem pushData_codeOfArgs {init : ByteArray} {as : List U256} {pc n : Nat}
    (h : pc + 1 + n ≤ init.size) : pushData (codeOfArgs init as) pc n = pushData init pc n := by
  unfold pushData codeOfArgs initArgs
  rw [bufferRead_append_of_le _ _ h]

theorem boundaryFrom_append {a b : ByteArray} {s p : Nat} (h : BoundaryFrom a s p) :
    BoundaryFrom (a ++ b) s p := by
  induction h with
  | here hs => exact .here (by rw [ByteArray.size_append]; omega)
  | @step s p hs _ ih =>
    have hn : nextOpcode (a ++ b) s = nextOpcode a s := by
      unfold nextOpcode
      rw [byteAt_append, if_pos hs]
    exact .step (by rw [ByteArray.size_append]; omega) (hn ▸ ih)

theorem validJumpDest_codeOfArgs {init : ByteArray} {as : List U256} {d : Nat}
    (h : isValidJumpDest (validJumpDestinations init) d = true) :
    isValidJumpDest (validJumpDestinations (codeOfArgs init as)) d = true := by
  rw [isValidJumpDest_iff_boundaryFrom] at h ⊢
  obtain ⟨hb, hj⟩ := h
  refine ⟨boundaryFrom_append hb, ?_⟩
  rw [byteAt_codeOfArgs_lt hb.bounds.2]
  exact hj

/-! ## The symbolic evaluator -/

/-- A symbolic frame: the program counter, the stack, the memory and the storage writes (concrete
keys), newest first. -/
structure SCfg where
  pc : Nat
  stack : List E
  mem : List B
  ws : List (U256 × E)

/-- A symbolic step: the next frame, its price and the path conditions it adds, or the returned
bytes and the price of the halt. -/
inductive SR where
  | next (c : SCfg) (cost : Nat) (conds : List E)
  | ret (out : List B) (cost : Nat)

/-- The concrete frame of a symbolic frame, for the argument words `as`. -/
def inst (as : List U256) (c : SCfg) : Cfg :=
  ⟨c.pc, c.stack.map (E.eval as), bytesOf as c.mem, c.ws.map fun p => (p.1, p.2.eval as)⟩

section Steps
variable (init : ByteArray) (n : Nat)

def tFamily (c : SCfg) (op : Op) : Option SR :=
  match binOf op with
  | some (k, f) =>
    match c.stack with
    | x :: y :: r => some (.next { c with pc := c.pc + 1, stack := mkBin op f x y :: r } k [])
    | _ => none
  | none =>
    match unOf op with
    | some (k, f) =>
      match c.stack with
      | x :: r => some (.next { c with pc := c.pc + 1, stack := mkUn op f x :: r } k [])
      | _ => none
    | none =>
      match op with
      | .push m =>
        if m.val ≠ 0 ∧ c.stack.length < STACK_LIMIT ∧ c.pc + 1 + m.val ≤ init.size then
          some (.next { c with pc := c.pc + (1 + m.val), stack := .c (pushData init c.pc m) :: c.stack } 3 [])
        else none
      | .dup m =>
        match c.stack[m.val]? with
        | some x =>
          if c.stack.length < STACK_LIMIT then
            some (.next { c with pc := c.pc + 1, stack := x :: c.stack } 3 [])
          else none
        | none => none
      | .swap m =>
        match c.stack with
        | top :: r =>
          match r[m.val]? with
          | some x => some (.next { c with pc := c.pc + 1, stack := x :: r.set m.val top } 3 [])
          | none => none
        | [] => none
      | _ => none

def tPush0 (c : SCfg) : Option SR :=
  if c.stack.length < STACK_LIMIT then some (.next { c with pc := c.pc + 1, stack := .c 0 :: c.stack } 2 [])
  else none

def tCodesize (c : SCfg) : Option SR :=
  if c.stack.length < STACK_LIMIT then
    some (.next { c with pc := c.pc + 1, stack := .c (BitVec.ofNat 256 (init.size + 32 * n)) :: c.stack } 2 [])
  else none

def tPop (c : SCfg) : Option SR :=
  match c.stack with
  | _ :: r => some (.next { c with pc := c.pc + 1, stack := r } 2 [])
  | [] => none

def tJump (c : SCfg) : Option SR :=
  match c.stack with
  | .c d :: r =>
    if isValidJumpDest (validJumpDestinations init) d.toNat = true then
      some (.next { c with pc := d.toNat, stack := r } 8 [])
    else none
  | _ => none

def tJumpi (c : SCfg) : Option SR :=
  match c.stack with
  | d :: .c x :: r =>
    if x = 0 then some (.next { c with pc := c.pc + 1, stack := r } 10 [])
    else
      match d with
      | .c d =>
        if isValidJumpDest (validJumpDestinations init) d.toNat = true then
          some (.next { c with pc := d.toNat, stack := r } 10 [])
        else none
      | _ => none
  | _ :: x :: r => some (.next { c with pc := c.pc + 1, stack := r } 10 [x])
  | _ => none

def tMload (c : SCfg) : Option SR :=
  match c.stack with
  | .c start :: r =>
    match load (lRead (lExt c.mem (.c 0) (extendMemory c.mem.length [(start, 32)]).expandBy) start.toNat 32) with
    | some e =>
      some (.next { c with
        pc := c.pc + 1
        stack := e :: r
        mem := lExt c.mem (.c 0) (extendMemory c.mem.length [(start, 32)]).expandBy }
        (3 + (extendMemory c.mem.length [(start, 32)]).cost) [])
    | none => none
  | _ => none

def tMstore (c : SCfg) : Option SR :=
  match c.stack with
  | .c start :: v :: r =>
    some (.next { c with
      pc := c.pc + 1
      stack := r
      mem := lWrite (lExt c.mem (.c 0) (extendMemory c.mem.length [(start, 32)]).expandBy)
        start.toNat (wbytes v) }
      (3 + (extendMemory c.mem.length [(start, 32)]).cost) [])
  | _ => none

def tCodecopy (c : SCfg) : Option SR :=
  match c.stack with
  | .c start :: .c off :: .c size :: r =>
    some (.next { c with
      pc := c.pc + 1
      stack := r
      mem := lWrite (lExt c.mem (.c 0) (extendMemory c.mem.length [(start, size)]).expandBy)
        start.toNat ((List.range size.toNat).map fun i => codeByte init n (off.toNat + i)) }
      (3 + 3 * wordCount size.toNat + (extendMemory c.mem.length [(start, size)]).cost) [])
  | _ => none

def tSstore (c : SCfg) : Option SR :=
  match c.stack with
  | .c key :: new :: r =>
    some (.next { c with pc := c.pc + 1, stack := r, ws := (key, new) :: c.ws } 22100 [])
  | _ => none

def tReturn (c : SCfg) : Option SR :=
  match c.stack with
  | .c start :: .c size :: _ =>
    some (.ret (lRead (lExt c.mem (.c 0) (extendMemory c.mem.length [(start, size)]).expandBy)
      start.toNat size.toNat) (extendMemory c.mem.length [(start, size)]).cost)
  | _ => none

/-- One symbolic step on the byte `b`, in the order of `stepB`. -/
def tStep (c : SCfg) (b : UInt8) : Option SR :=
  if b = 0x5f then tPush0 c
  else if b = 0x34 then tPush0 c
  else if b = 0x38 then tCodesize init n c
  else if b = 0x50 then tPop c
  else if b = 0x5b then some (.next { c with pc := c.pc + 1 } 1 [])
  else if b = 0x56 then tJump init c
  else if b = 0x57 then tJumpi init c
  else if b = 0x51 then tMload c
  else if b = 0x52 then tMstore c
  else if b = 0x39 then tCodecopy init n c
  else if b = 0x55 then tSstore c
  else if b = 0xf3 then tReturn c
  else
    match Op.ofByte .fusaka b with
    | some op => tFamily init c op
    | none => none

/-- The symbolic evaluator: at most `fuel` steps of the init code from `c`, to the returned bytes,
the storage writes, the price of the run and its path conditions. -/
def symRun : Nat → SCfg → Option (List B × List (U256 × E) × Nat × List E)
  | 0, _ => none
  | fuel + 1, c =>
    if h : c.pc < init.size then
      match tStep init n c init[c.pc] with
      | some (.next c' k cs) =>
        match symRun fuel c' with
        | some (o, ws, m, cs') => some (o, ws, k + m, cs ++ cs')
        | none => none
      | some (.ret o k) => some (o, c.ws, k, [])
      | none => none
    else none

end Steps

/-! ## Soundness: each symbolic step is the concrete step -/

/-- What a symbolic step says of the concrete step `r`, for the argument words `as`. -/
def Sim (as : List U256) : SR → Option R → Prop
  | .next c' k cs, r => (∀ e ∈ cs, e.eval as = 0) → r = some (.next (inst as c') k)
  | .ret o k, r => r = some (.ret (bytesOf as o) k)

section Sound
variable {init : ByteArray} {as : List U256}

theorem bytesOf_size (m : List B) : (bytesOf as m).size = m.length := by
  simp [bytesOf, ba_size]

theorem ext_eval (m : List B) (k : Nat) :
    memoryExtend (bytesOf as m) k = bytesOf as (lExt m (.c 0) k) := by
  simp only [bytesOf, memoryExtend_ba, map_lExt]; rfl

theorem tPush0_sound (c : SCfg) {r : SR} (h : tPush0 c = some r) : Sim as r (sPush0 (inst as c)) := by
  unfold tPush0 at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq] at h; subst h
    intro _
    simp only [sPush0, inst, List.length_map]
    rw [if_pos hl] <;> rfl
  · simp at h

theorem tCodesize_sound (c : SCfg) {r : SR} (h : tCodesize init as.length c = some r) :
    Sim as r (sCodesize (codeOfArgs init as) (inst as c)) := by
  unfold tCodesize at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq] at h; subst h
    intro _
    simp only [sCodesize, inst, List.length_map]
    rw [if_pos hl, codeOfArgs_size] <;> rfl
  · simp at h

theorem tPop_sound (c : SCfg) {r : SR} (h : tPop c = some r) : Sim as r (sPop (inst as c)) := by
  unfold tPop at h
  split at h
  · rename_i x rest hs
    simp only [Option.some.injEq] at h; subst h
    intro _
    simp only [sPop, inst, hs, List.map_cons]
  · simp at h

theorem tJump_sound (c : SCfg) {r : SR} (h : tJump init c = some r) :
    Sim as r (sJump (codeOfArgs init as) (inst as c)) := by
  unfold tJump at h
  split at h
  · rename_i d rest hs
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h; subst h
      intro _
      simp only [sJump, inst, hs, List.map_cons, E.eval]
      rw [if_pos (validJumpDest_codeOfArgs hv)] <;> rfl
    · simp at h
  · simp at h

theorem tJumpi_sound (c : SCfg) {r : SR} (h : tJumpi init c = some r) :
    Sim as r (sJumpi (codeOfArgs init as) (inst as c)) := by
  unfold tJumpi at h
  split at h
  · rename_i d x rest hs
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h; subst h
      intro _
      simp only [sJumpi, inst, hs, List.map_cons, E.eval]
      rw [if_pos hx] <;> rfl
    · rename_i hx
      split at h
      · rename_i d'
        split at h
        · rename_i hv
          simp only [Option.some.injEq] at h; subst h
          intro _
          simp only [sJumpi, inst, hs, List.map_cons, E.eval]
          rw [if_neg hx, if_pos (validJumpDest_codeOfArgs hv)] <;> rfl
        · simp at h
      · simp at h
  · rename_i d x rest _ hs
    simp only [Option.some.injEq] at h; subst h
    intro hc
    have hx : x.eval as = 0 := hc x (by simp)
    simp only [sJumpi, inst, hs, List.map_cons]
    rw [if_pos hx] <;> rfl
  · simp at h

theorem tMload_sound (c : SCfg) {r : SR} (h : tMload c = some r) : Sim as r (sMload (inst as c)) := by
  unfold tMload at h
  split at h
  · rename_i start rest hs
    split at h
    · rename_i e he
      simp only [Option.some.injEq] at h; subst h
      intro _
      simp only [sMload, inst, hs, List.map_cons, E.eval]
      rw [bytesOf_size, ext_eval, bytesOf, memoryReadBytes_ba, ← map_lRead]
      rw [show ba ((lRead _ start.toNat 32).map (B.eval as)) = bytesOf as (lRead _ start.toNat 32)
        from rfl, load_eval he]
    · simp at h
  · simp at h

theorem tMstore_sound (c : SCfg) {r : SR} (h : tMstore c = some r) : Sim as r (sMstore (inst as c)) := by
  unfold tMstore at h
  split at h
  · rename_i start v rest hs
    simp only [Option.some.injEq] at h; subst h
    intro _
    simp only [sMstore, inst, hs, List.map_cons, E.eval]
    rw [bytesOf_size, ext_eval, ← wbytes_eval, bytesOf, bytesOf, memoryWrite_ba, ← map_lWrite] <;> rfl
  · simp at h

theorem tCodecopy_sound (c : SCfg) {r : SR} (h : tCodecopy init as.length c = some r) :
    Sim as r (sCodecopy (codeOfArgs init as) (inst as c)) := by
  unfold tCodecopy at h
  split at h
  · rename_i start off size rest hs
    simp only [Option.some.injEq] at h; subst h
    intro _
    simp only [sCodecopy, inst, hs, List.map_cons, E.eval]
    rw [bytesOf_size, ext_eval, ← bufferRead_codeOfArgs]
    rw [show (⟨(List.map (B.eval as) (List.map (fun i => codeByte init as.length (off.toNat + i))
      (List.range size.toNat))).toArray⟩ : ByteArray) = ba _ from rfl, bytesOf, memoryWrite_ba,
      ← map_lWrite]
    rfl
  · simp at h

theorem tSstore_sound (c : SCfg) {r : SR} (h : tSstore c = some r) : Sim as r (sSstore (inst as c)) := by
  unfold tSstore at h
  split at h
  · rename_i key v rest hs
    simp only [Option.some.injEq] at h; subst h
    intro _
    simp only [sSstore, inst, hs, List.map_cons, E.eval]
  · simp at h

theorem tReturn_sound (c : SCfg) {r : SR} (h : tReturn c = some r) : Sim as r (sReturn (inst as c)) := by
  unfold tReturn at h
  split at h
  · rename_i start size rest hs
    simp only [Option.some.injEq] at h; subst h
    simp only [Sim, sReturn, inst, hs, List.map_cons, E.eval]
    rw [bytesOf_size, ext_eval, bytesOf, memoryReadBytes_ba, ← map_lRead] <;> rfl
  · simp at h

theorem tFamily_sound (c : SCfg) (op : Op) {r : SR} (h : tFamily init c op = some r) :
    Sim as r (family (codeOfArgs init as) (inst as c) op) := by
  unfold tFamily at h
  repeat' split at h
  all_goals try (simp at h; done)
  all_goals simp only [Option.some.injEq] at h; subst h; intro _
  · simp only [family, ‹binOf _ = _›, inst, ‹c.stack = _›, List.map_cons]
    rw [mkBin_eval ‹_›]
  · simp only [family, ‹binOf _ = _›, ‹unOf _ = _›, inst, ‹c.stack = _›, List.map_cons]
    rw [mkUn_eval ‹_›]
  · rename_i hc _
    simp only [family, ‹binOf _ = _›, ‹unOf _ = _›, inst, List.length_map]
    rw [if_pos ⟨hc.1, hc.2.1⟩, pushData_codeOfArgs hc.2.2] <;> rfl
  · simp only [family, ‹binOf _ = _›, ‹unOf _ = _›, inst, List.getElem?_map, ‹c.stack[_]? = _›,
      Option.map_some, List.length_map]
    rw [if_pos ‹_›] <;> rfl
  · simp only [family, ‹binOf _ = _›, ‹unOf _ = _›, inst, ‹c.stack = _›, List.map_cons,
      List.getElem?_map, ‹_[_]? = _›, Option.map_some, List.map_set]

theorem tStep_sound (c : SCfg) (b : UInt8) {r : SR} (h : tStep init as.length c b = some r) :
    Sim as r (stepB (codeOfArgs init as) (inst as c) b) := by
  unfold tStep at h
  unfold stepB
  by_cases h0 : b = 0x5f
  · rw [if_pos h0] at h ⊢; exact tPush0_sound c h
  rw [if_neg h0] at h ⊢
  by_cases h1 : b = 0x34
  · rw [if_pos h1] at h ⊢; exact tPush0_sound c h
  rw [if_neg h1] at h ⊢
  by_cases h2 : b = 0x38
  · rw [if_pos h2] at h ⊢; exact tCodesize_sound c h
  rw [if_neg h2] at h ⊢
  by_cases h3 : b = 0x50
  · rw [if_pos h3] at h ⊢; exact tPop_sound c h
  rw [if_neg h3] at h ⊢
  by_cases h4 : b = 0x5b
  · rw [if_pos h4] at h ⊢; simp only [Option.some.injEq] at h; subst h; intro _; rfl
  rw [if_neg h4] at h ⊢
  by_cases h5 : b = 0x56
  · rw [if_pos h5] at h ⊢; exact tJump_sound c h
  rw [if_neg h5] at h ⊢
  by_cases h6 : b = 0x57
  · rw [if_pos h6] at h ⊢; exact tJumpi_sound c h
  rw [if_neg h6] at h ⊢
  by_cases h7 : b = 0x51
  · rw [if_pos h7] at h ⊢; exact tMload_sound c h
  rw [if_neg h7] at h ⊢
  by_cases h8 : b = 0x52
  · rw [if_pos h8] at h ⊢; exact tMstore_sound c h
  rw [if_neg h8] at h ⊢
  by_cases h9 : b = 0x39
  · rw [if_pos h9] at h ⊢; exact tCodecopy_sound c h
  rw [if_neg h9] at h ⊢
  by_cases h10 : b = 0x55
  · rw [if_pos h10] at h ⊢; exact tSstore_sound c h
  rw [if_neg h10] at h ⊢
  by_cases h11 : b = 0xf3
  · rw [if_pos h11] at h ⊢; exact tReturn_sound c h
  rw [if_neg h11] at h ⊢
  split at h
  · rename_i op hop
    rw [hop]
    exact tFamily_sound c op h
  · simp at h

/-- **The symbolic run is the concrete run, for every argument list.** Whenever the symbolic
evaluator runs `init` to RETURN with the path conditions `cs`, the concrete evaluator runs the
creation code `initArgs init ws` of every argument list `ws` of that length whose words meet
`cs` to the same bytes, writes and price. -/
theorem symRun_sound : ∀ (fuel : Nat) (c : SCfg) {o : List B} {ws : List (U256 × E)} {m : Nat}
    {cs : List E}, symRun init as.length fuel c = some (o, ws, m, cs) → (∀ e ∈ cs, e.eval as = 0) →
    run (codeOfArgs init as) fuel (inst as c) =
      some (bytesOf as o, ws.map (fun p => (p.1, p.2.eval as)), m)
  | 0, c, _, _, _, _, h, _ => by simp [symRun] at h
  | fuel + 1, c, o, ws, m, cs, h, hcs => by
    unfold symRun at h
    split at h
    · rename_i hlt
      have hlt' : (inst as c).pc < (codeOfArgs init as).size := by
        simp only [inst, codeOfArgs_size]; omega
      have hb : (codeOfArgs init as)[(inst as c).pc] = init[c.pc] :=
        getElem_codeOfArgs (as := as) hlt hlt'
      unfold run
      rw [dif_pos hlt', hb]
      split at h
      · rename_i c' k cs1 hstep
        split at h
        · rename_i o' ws' m' cs2 hrun
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have h1 : ∀ e ∈ cs1, e.eval as = 0 := fun e he => hcs e (List.mem_append_left _ he)
          have h2 : ∀ e ∈ cs2, e.eval as = 0 := fun e he => hcs e (List.mem_append_right _ he)
          rw [tStep_sound c _ hstep h1]
          dsimp only
          rw [symRun_sound fuel c' hrun h2]
        · simp at h
      · rename_i o' k hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        rw [tStep_sound c _ hstep] <;> rfl
      · simp at h
    · simp at h

end Sound

/-! ## Deployment for every argument list, from one check -/

/-- The word a storage key holds after the symbolic writes, newest first. -/
def slook : List (U256 × E) → U256 → E
  | [], _ => .c 0
  | (a, v) :: r, k => if a = k then v else slook r k

/-- The symbolic word a storage specification gives a slot, as `slotValue` reads it. -/
def sslot (s : List (Nat × E)) (slot : Nat) : E :=
  s.foldl (fun acc kv => if kv.1 % 2^256 = slot % 2^256 then kv.2 else acc) (.c 0)

/-- The storage a specification gives for the argument words `as`. -/
def storeOf (as : List U256) (s : List (Nat × E)) : List (Nat × Nat) :=
  s.map fun kv => (kv.1, (kv.2.eval as).toNat)

/-- The runtime code a specification gives for the argument words `as`. -/
def codeOf (as : List U256) (code : List B) : ByteArray := bytesOf as code

/-- Whether the symbolic writes and the specification `s` give the same word at every key either
names. -/
def sKeysOk (ws : List (U256 × E)) (s : List (Nat × E)) : Bool :=
  (ws.map Prod.fst ++ s.map fun p => BitVec.ofNat 256 p.1).all fun k => slook ws k == sslot s k.toNat

/-- Whether the symbolic evaluator runs `init`, with `n` argument words, within the gas of the
creation to the runtime bytes `code` and the storage `s`, with no path condition outside `pre`. -/
def symCheck (fuel : Nat) (init : ByteArray) (n : Nat) (pre : List E) (code : List B)
    (s : List (Nat × E)) : Bool :=
  match symRun init n fuel ⟨0, [], [], []⟩ with
  | some (o, ws, m, cs) =>
    decide (m ≤ 10000000) && o == code && cs.all (fun e => decide (e ∈ pre)) && sKeysOk ws s
  | none => false

theorem slook_eval (as : List U256) : ∀ (ws : List (U256 × E)) (k : U256),
    look (ws.map fun p => (p.1, p.2.eval as)) k = (slook ws k).eval as
  | [], _ => rfl
  | (a, v) :: r, k => by
    simp only [List.map_cons, look, slook]
    split
    · rfl
    · exact slook_eval as r k

theorem sslot_eval (as : List U256) (s : List (Nat × E)) (slot : Nat) :
    SolarTV.slotValue (storeOf as s) slot = ((sslot s slot).eval as).toNat := by
  unfold SolarTV.slotValue storeOf sslot
  suffices ∀ (acc : E) (l : List (Nat × E)),
      (l.map fun kv => (kv.1, (kv.2.eval as).toNat)).foldl
        (fun acc kv => if kv.1 % 2^256 = slot % 2^256 then kv.2 % 2^256 else acc) ((acc.eval as).toNat) =
      ((l.foldl (fun acc kv => if kv.1 % 2^256 = slot % 2^256 then kv.2 else acc) acc).eval as).toNat by
    exact this (.c 0) s
  intro acc l
  induction l generalizing acc with
  | nil => rfl
  | cons kv r ih =>
    simp only [List.map_cons, List.foldl_cons]
    split
    · rw [Nat.mod_eq_of_lt (kv.2.eval as).isLt]
      exact ih kv.2
    · exact ih acc

theorem keysOk_of_sKeysOk {as : List U256} {ws : List (U256 × E)} {s : List (Nat × E)}
    (h : sKeysOk ws s = true) : keysOk (ws.map fun p => (p.1, p.2.eval as)) (storeOf as s) = true := by
  simp only [sKeysOk, List.all_eq_true, beq_iff_eq] at h
  simp only [keysOk, List.all_eq_true, beq_iff_eq]
  intro k hk
  have hk' : k ∈ ws.map Prod.fst ++ s.map fun p => BitVec.ofNat 256 p.1 := by
    simpa [storeOf, List.map_map, Function.comp_def] using hk
  rw [slook_eval, sslot_eval, h k hk']

/-- The bytes of a byte array, read one by one, are the bytes of its array. -/
theorem toList_eq_data_toList' (bs : ByteArray) : bs.toList = bs.data.toList := by
  have hs : bs.data.toList.length = bs.size := Array.length_toList
  have loop : ∀ i r, i ≤ bs.size →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro i r hi
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r hlt ih =>
        rw [ih (by omega)]
        have hget : bs.get! i = bs.data.toList[i]'(by omega) := by
          obtain ⟨a⟩ := bs
          exact (getElem!_pos a i hlt).trans (Array.getElem_toList _).symm
        rw [hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          ← List.drop_eq_getElem_cons]
    | case2 i r hge =>
        rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  unfold ByteArray.toList
  simpa using loop 0 [] (Nat.zero_le _)

/-- **Deployment for every argument list, from the symbolic check**: one kernel evaluation of
`symCheck` gives `Deploys` for every list of `n` argument words that meets the path conditions
`pre`, with the runtime code `codeOf as code` and the storage `storeOf as s`. -/
theorem deploys_all {fuel : Nat} {init : ByteArray} {n : Nat} {pre : List E} {code : List B}
    {s : List (Nat × E)} (h : symCheck fuel init n pre code s = true) (as : List U256)
    (hn : as.length = n) (hpre : ∀ e ∈ pre, e.eval as = 0) :
    Deploys (initArgs init (as.map BitVec.toNat)) (codeOf as code) (storeOf as s) := by
  subst hn
  unfold symCheck at h
  split at h
  · rename_i o ws m cs hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hm, rfl⟩, hcs⟩, hk⟩ := h
    have hrun : run (initArgs init (as.map BitVec.toNat)) fuel initCfg =
        some (bytesOf as o, ws.map (fun p => (p.1, p.2.eval as)), m) :=
      symRun_sound (as := as) fuel ⟨0, [], [], []⟩ hr (fun e he => hpre e (hcs e he))
    obtain ⟨obs, hobs, hs, hout, hst⟩ := observes fuel hrun hm
    exact ⟨obs, hobs, hs, by rw [hout, toList_eq_data_toList']; rfl,
      fun k => by rw [hst, keysOk_slot (keysOk_of_sKeysOk hk)]⟩
  · simp at h

/-- info: 'Verify.Lifecycle.Creation.Sym.deploys_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploys_all

/-! ## Runtime code with patched immutables -/

/-- solar's runtime code `rt` with each `(offset, word)` of `ps` written over it, in order. -/
def patched (rt : ByteArray) (ps : List (Nat × E)) : List B :=
  ps.foldl (fun l p => lWrite l p.1 (wbytes p.2)) (rt.data.toList.map B.c)

theorem codeOf_patched (as : List U256) (rt : ByteArray) (ps : List (Nat × E)) :
    codeOf as (patched rt ps) = ps.foldl (fun c p => patchWord c p.1 (p.2.eval as)) rt := by
  unfold codeOf patched
  suffices ∀ (l : List B) (c : ByteArray), bytesOf as l = c →
      bytesOf as (ps.foldl (fun l p => lWrite l p.1 (wbytes p.2)) l) =
        ps.foldl (fun c p => patchWord c p.1 (p.2.eval as)) c by
    apply this
    apply ba_ext
    simp [bytesOf, ba, B.eval, List.map_map, Function.comp_def]
  intro l c hl
  induction ps generalizing l c with
  | nil => simpa using hl
  | cons p r ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [← hl, patchWord, ← wbytes_eval, bytesOf, bytesOf, bytesOf, memoryWrite_ba, map_lWrite]

/-- info: 'Verify.Lifecycle.Creation.Sym.codeOf_patched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms codeOf_patched

/-! ## The specification of a creation, read off its symbolic run -/

/-- The symbolic run of the init code `init` with `n` argument words, from the empty frame. -/
def spec? (fuel : Nat) (init : ByteArray) (n : Nat) :
    Option (List B × List (U256 × E) × Nat × List E) :=
  symRun init n fuel ⟨0, [], [], []⟩

/-- The run's path conditions: the argument words a creation needs to take the symbolic path. -/
def specPre (fuel : Nat) (init : ByteArray) (n : Nat) : List E :=
  match spec? fuel init n with
  | some (_, _, _, cs) => cs
  | none => []

/-- The run's returned bytes: the runtime code, as a function of the argument words. -/
def specCode (fuel : Nat) (init : ByteArray) (n : Nat) : List B :=
  match spec? fuel init n with
  | some (o, _, _, _) => o
  | none => []

/-- The run's storage writes, oldest first, as a function of the argument words. -/
def specStore (fuel : Nat) (init : ByteArray) (n : Nat) : List (Nat × E) :=
  match spec? fuel init n with
  | some (_, ws, _, _) => ws.reverse.map fun p => (p.1.toNat, p.2)
  | none => []

/-- Whether the symbolic run of `init` proves its own specification. -/
def allArgsCheck (fuel : Nat) (init : ByteArray) (n : Nat) : Bool :=
  symCheck fuel init n (specPre fuel init n) (specCode fuel init n) (specStore fuel init n)

/-- **Every creation of `init`, from one check**: when `allArgsCheck` holds, every list of `n`
argument words that meets the run's path conditions deploys the runtime code `specCode` and the
storage `specStore` read at those words. -/
theorem deploys_allArgs {fuel : Nat} {init : ByteArray} {n : Nat}
    (h : allArgsCheck fuel init n = true) (as : List U256) (hn : as.length = n)
    (hpre : ∀ e ∈ specPre fuel init n, e.eval as = 0) :
    Deploys (initArgs init (as.map BitVec.toNat)) (codeOf as (specCode fuel init n))
      (storeOf as (specStore fuel init n)) :=
  deploys_all h as hn hpre

/-! ## Storage compared slot by slot -/

/-- Whether two storages give the same word at every key either names. -/
def sameSlots (a b : List (Nat × Nat)) : Bool :=
  (a.map Prod.fst ++ b.map Prod.fst).all fun k => SolarTV.slotValue a k == SolarTV.slotValue b k

theorem slotValue_key (s : List (Nat × Nat)) {k k' : Nat} (h : k % 2 ^ 256 = k' % 2 ^ 256) :
    SolarTV.slotValue s k = SolarTV.slotValue s k' := by
  simp only [SolarTV.slotValue, h]

theorem slotValue_eq_of_sameSlots {a b : List (Nat × Nat)} (h : sameSlots a b = true) (k : Nat) :
    SolarTV.slotValue a k = SolarTV.slotValue b k := by
  simp only [sameSlots, List.all_eq_true, beq_iff_eq] at h
  by_cases hk : ∃ p ∈ a.map Prod.fst ++ b.map Prod.fst, p % 2 ^ 256 = k % 2 ^ 256
  · obtain ⟨p, hp, he⟩ := hk
    rw [slotValue_key a he.symm, slotValue_key b he.symm]
    exact h p hp
  · have hn : ∀ (s : List (Nat × Nat)), (∀ q ∈ s.map Prod.fst, q % 2 ^ 256 ≠ k % 2 ^ 256) →
        SolarTV.slotValue s k = 0 := fun s hs =>
      foldl_slot_eq (fun p hp => hs p.1 (List.mem_map_of_mem hp))
    rw [hn a (fun q hq he => hk ⟨q, List.mem_append_left _ hq, he⟩),
      hn b (fun q hq he => hk ⟨q, List.mem_append_right _ hq, he⟩)]

theorem deploys_congr {init code : ByteArray} {s s' : List (Nat × Nat)} (h : Deploys init code s)
    (hs : sameSlots s s' = true) : Deploys init code s' := by
  obtain ⟨o, hr, hok, hout, hst⟩ := h
  exact ⟨o, hr, hok, hout, fun k => by rw [hst, slotValue_eq_of_sameSlots hs]⟩

/-! ## One creation as an instance of every creation -/

/-- Whether the argument words `as` are `ws`, meet the run's path conditions, and give the runtime
code `code` and a storage that agrees with `s` at every slot. -/
def atArgsCheck (fuel : Nat) (init : ByteArray) (n : Nat) (as : List U256) (ws : List Nat)
    (code : ByteArray) (s : List (Nat × Nat)) : Bool :=
  decide (as.length = n) && as.map BitVec.toNat == ws &&
    (specPre fuel init n).all (fun e => e.eval as == 0) &&
    (codeOf as (specCode fuel init n)).data.toList == code.data.toList &&
    sameSlots (storeOf as (specStore fuel init n)) s

/-- A creation with concrete argument words, as the instance of `deploys_allArgs` at them. -/
theorem deploys_at {fuel : Nat} {init : ByteArray} {n : Nat} {as : List U256} {ws : List Nat}
    {code : ByteArray} {s : List (Nat × Nat)} (h : allArgsCheck fuel init n = true)
    (h' : atArgsCheck fuel init n as ws code s = true) : Deploys (initArgs init ws) code s := by
  simp only [atArgsCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h'
  obtain ⟨⟨⟨⟨hn, hws⟩, hpre⟩, hcode⟩, hs⟩ := h'
  have d := deploys_allArgs h as hn hpre
  rw [hws, ba_ext hcode] at d
  exact deploys_congr d hs

/-- info: 'Verify.Lifecycle.Creation.Sym.deploys_allArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploys_allArgs

/-- info: 'Verify.Lifecycle.Creation.Sym.deploys_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploys_at

end Verify.Lifecycle.Creation.Sym
