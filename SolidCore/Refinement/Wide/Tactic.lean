import Lean
import SolidCore.Solidity.Checked

/-!
# A symbolic evaluator for SolidCore's interpreter

SolidCore's interpreter (`SolidCore.Solidity.Interpreter`) is an ordinary Lean
function: structural recursion on fuel and on the syntax, over `Nat` words, in
the interaction monad `SolI`. For a fixed contract and a call whose argument
words are free variables, everything but the arithmetic on those variables is
concrete, so `simp` can run the interpreter: it unfolds each definition when it
meets it, reduces the matches and `if`s whose discriminants become constructors
or decidable ground facts, and leaves the terms on the free words.

`src_eval [lemmas]` does that to a fixed point. Each round it collects the
definitions of the interpreter (`SolidCore.Solidity.Source`, `SolidCore.Solidity.Shared`
and the interaction monad `EvmCompiler.Simulation.Interaction`), the monad helpers
and the instances of the monad classes that occur in the goal, adds their
equations to `simp`'s set, and simplifies with them, the lemmas given, the
hypotheses in context, `monadLemmas`, which turn the monad operations of `SolI`,
`Except` and `Option` into their definitions, and `wordLemmas`. It unfolds only
what occurs, so it generates equations for the few hundred definitions a call
reaches rather than for the thousands the interpreter has. Definitions by
well-founded recursion stay folded, since their equations would unfold forever.

`src_symex [lemmas]` adds path splitting: when the goal no longer simplifies,
it splits on the innermost condition of an `if` it still holds (`by_cases`), or else
on its first `match` (`split`), and continues on each branch with the branch
condition as a hypothesis that later rounds rewrite with. A branch whose
conditions contradict each other by `omega` is closed. It leaves a branch that
neither simplifies nor splits to the caller.

`wordLemmas` are the facts about a 256-bit word `w.toNat` the evaluator needs
to see that SolidCore's normalisation of words does not change it, and the
bounds of `&&&`, `^^^` and `|||` at each byte width (`widthLemmas`), which
discharge the range checks of SolidCore's casts and cleanups.

Measured on the corpus: unfolding every definition of the interpreter up front
(1119 to 1844 of them) fails, since generating their equations exceeds the
recursion and heartbeat limits; unfolding on demand reaches a fixed point in
about 15 rounds and 240 definitions for `w1`.
-/

open Lean Meta Elab Tactic

namespace SolidCore.Refinement.Wide

/-- The name prefixes whose definitions the source evaluator unfolds. -/
def evalPrefixes : List Name :=
  [`SolidCore.Solidity.Source, `SolidCore.Solidity.Shared, `EvmCompiler.Simulation.Interaction]

/-- Whether `n` is a definition of the interpreter: in one of `evalPrefixes`, and not an
auxiliary or a matcher. -/
def interpreterDef (env : Environment) (n : Name) : Option ConstantInfo :=
  match env.find? n with
  | some ci@(.defnInfo _) =>
    if evalPrefixes.any (·.isPrefixOf n) && !n.isInternalDetail && !isAuxRecursor env n &&
        !isNoConfusion env n && !(Meta.isMatcherCore env n) then some ci else none
  | _ => none

/-- Whether the evaluator unfolds `n`: a definition of the interpreter that is not by
well-founded recursion, or one by well-founded recursion that matches on its arguments, so
that each of its several equations fires only on its constructors. An unconditional equation
of a function by well-founded recursion would unfold forever. -/
def unfoldable (n : Name) : MetaM Bool := do
  let some ci := interpreterDef (← getEnv) n | return false
  unless ci.value!.getUsedConstants.contains ``WellFounded.fix do return true
  match ← tryCatchRuntimeEx (getEqnsFor? n) (fun _ => pure none) with
  | some eqs => return eqs.size > 1
  | none => return false

/-- The monad classes whose instances the evaluator unfolds. -/
def monadClasses : List Name :=
  [`Monad, `Bind, `Pure, `Functor, `Applicative, `Seq, `SeqLeft, `SeqRight, `MonadLift,
   `MonadLiftT, `MonadExcept, `MonadExceptOf, `MonadFunctor, `MonadFunctorT]

/-- Monad and option helpers the evaluator unfolds. -/
def monadHelpers : List Name :=
  [`liftM, `Except.map, `Except.bind, `Except.pure, `Except.tryCatch, `Except.mapError,
   `Function.comp, `Option.bind, `Option.map, `Option.getD, `Option.orElse, `Option.isSome,
   `Option.isNone]

/-- Whether `n` is an instance of one of the monad classes. -/
def isMonadInstance (n : Name) : MetaM Bool := do
  unless isInstanceCore (← getEnv) n do return false
  let ci ← getConstInfo n
  forallTelescopeReducing ci.type fun _ body => do
    let body ← whnfR body
    return monadClasses.contains body.getAppFn.constName

/-- The constants of `e` the evaluator unfolds. -/
def unfoldableIn (e : Expr) : MetaM NameSet := do
  let mut s : NameSet := {}
  for n in e.getUsedConstants do
    if (← unfoldable n) || monadHelpers.contains n || (← isMonadInstance n) then
      s := s.insert n
  return s

section MonadLemmas

open EvmCompiler.Simulation SolidCore.Solidity.Source

variable {E α β : Type}

theorem interaction_bind (x : Interaction E α) (f : α → Interaction E β) :
    x >>= f = Interaction.bind x f := rfl
theorem interaction_pure (a : α) : (pure a : Interaction E α) = .done (.ok a) := rfl
theorem interaction_map (f : α → β) (x : Interaction E α) :
    f <$> x = Interaction.bind x (fun a => .done (.ok (f a))) := rfl
theorem interaction_throw (e : E) : (throw e : Interaction E α) = .done (.error e) := rfl
theorem interaction_tryCatch (x : Interaction E α) (h : E → Interaction E α) :
    tryCatch x h = Interaction.tryCatch x h := rfl
theorem interaction_tryCatchThe (x : Interaction E α) (h : E → Interaction E α) :
    tryCatchThe E x h = Interaction.tryCatch x h := rfl
theorem solI_lift (x : Except RevertData α) : (monadLift x : SolI α) = SolI.ofExcept x := rfl
theorem solI_liftM (x : Except RevertData α) : (liftM x : SolI α) = SolI.ofExcept x := rfl
theorem except_bind {ε : Type} (x : Except ε α) (f : α → Except ε β) :
    x >>= f = Except.bind x f := rfl
theorem except_pure {ε : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
theorem except_map {ε : Type} (f : α → β) (x : Except ε α) : f <$> x = Except.map f x := rfl
theorem except_throw {ε : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl
theorem option_bind (x : Option α) (f : α → Option β) : x >>= f = Option.bind x f := rfl
theorem option_pure (a : α) : (pure a : Option α) = some a := rfl
theorem option_map (f : α → β) (x : Option α) : f <$> x = Option.map f x := rfl

end MonadLemmas

/-- The monad lemmas the evaluator always uses. -/
def monadLemmas : List Name :=
  [``interaction_bind, ``interaction_pure, ``interaction_map, ``interaction_throw,
   ``interaction_tryCatch, ``interaction_tryCatchThe, ``solI_lift, ``solI_liftM,
   ``except_bind, ``except_pure, ``except_map, ``except_throw, ``option_bind,
   ``option_pure, ``option_map]

/-! ## Words -/

/-- The number of 256-bit words, as the literal `simp` reduces `2 ^ 256` to. -/
abbrev wordCount : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

theorem uint256_size : EvmYul.UInt256.size = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := rfl
theorem wordModulus_eq : SolidCore.Solidity.Shared.wordModulus = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := rfl
theorem toNat_mod_word (w : BitVec 256) : w.toNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = w.toNat :=
  Nat.mod_eq_of_lt w.isLt
theorem toNat_lt_word (w : BitVec 256) : w.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := w.isLt
theorem not_word_le_toNat (w : BitVec 256) : ¬ 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤ w.toNat := Nat.not_le.mpr w.isLt
theorem mod_word_lt (x : Nat) : x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := Nat.mod_lt _ (by decide)
theorem not_word_le_mod (x : Nat) : ¬ 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤ x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := Nat.not_le.mpr (Nat.mod_lt _ (by decide))

theorem ite_mod_word (p : Prop) [Decidable p] (a b : Nat) :
    (if p then a else b) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = if p then a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 else b % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  split <;> rfl

theorem mod_mod_of_le (x m n : Nat) (hm : 0 < m) (h : m ≤ n) : x % m % n = x % m :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hm) h)

theorem mod_lt_of_le (x m n : Nat) (hm : 0 < m) (h : m ≤ n) : x % m < n :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ hm) h

theorem and_lt_of_lt (a b m : Nat) (ha : a < m) : a &&& b < m :=
  Nat.lt_of_le_of_lt Nat.and_le_left ha

/-! The bounds of `^^^` and `|||` on words of each width that is a whole number of bytes, with
the width's number of words as the literal `simp` reduces `2 ^ k` to. -/

theorem xor_lt_8 (a b : Nat) (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 :=
  Nat.xor_lt_two_pow (n := 8) ha hb

theorem or_lt_8 (a b : Nat) (ha : a < 256) (hb : b < 256) : a ||| b < 256 :=
  Nat.or_lt_two_pow (n := 8) ha hb

theorem xor_lt_16 (a b : Nat) (ha : a < 65536) (hb : b < 65536) : a ^^^ b < 65536 :=
  Nat.xor_lt_two_pow (n := 16) ha hb

theorem or_lt_16 (a b : Nat) (ha : a < 65536) (hb : b < 65536) : a ||| b < 65536 :=
  Nat.or_lt_two_pow (n := 16) ha hb

theorem xor_lt_24 (a b : Nat) (ha : a < 16777216) (hb : b < 16777216) : a ^^^ b < 16777216 :=
  Nat.xor_lt_two_pow (n := 24) ha hb

theorem or_lt_24 (a b : Nat) (ha : a < 16777216) (hb : b < 16777216) : a ||| b < 16777216 :=
  Nat.or_lt_two_pow (n := 24) ha hb

theorem xor_lt_32 (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) : a ^^^ b < 4294967296 :=
  Nat.xor_lt_two_pow (n := 32) ha hb

theorem or_lt_32 (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) : a ||| b < 4294967296 :=
  Nat.or_lt_two_pow (n := 32) ha hb

theorem xor_lt_40 (a b : Nat) (ha : a < 1099511627776) (hb : b < 1099511627776) : a ^^^ b < 1099511627776 :=
  Nat.xor_lt_two_pow (n := 40) ha hb

theorem or_lt_40 (a b : Nat) (ha : a < 1099511627776) (hb : b < 1099511627776) : a ||| b < 1099511627776 :=
  Nat.or_lt_two_pow (n := 40) ha hb

theorem xor_lt_48 (a b : Nat) (ha : a < 281474976710656) (hb : b < 281474976710656) : a ^^^ b < 281474976710656 :=
  Nat.xor_lt_two_pow (n := 48) ha hb

theorem or_lt_48 (a b : Nat) (ha : a < 281474976710656) (hb : b < 281474976710656) : a ||| b < 281474976710656 :=
  Nat.or_lt_two_pow (n := 48) ha hb

theorem xor_lt_56 (a b : Nat) (ha : a < 72057594037927936) (hb : b < 72057594037927936) : a ^^^ b < 72057594037927936 :=
  Nat.xor_lt_two_pow (n := 56) ha hb

theorem or_lt_56 (a b : Nat) (ha : a < 72057594037927936) (hb : b < 72057594037927936) : a ||| b < 72057594037927936 :=
  Nat.or_lt_two_pow (n := 56) ha hb

theorem xor_lt_64 (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) : a ^^^ b < 18446744073709551616 :=
  Nat.xor_lt_two_pow (n := 64) ha hb

theorem or_lt_64 (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) : a ||| b < 18446744073709551616 :=
  Nat.or_lt_two_pow (n := 64) ha hb

theorem xor_lt_72 (a b : Nat) (ha : a < 4722366482869645213696) (hb : b < 4722366482869645213696) : a ^^^ b < 4722366482869645213696 :=
  Nat.xor_lt_two_pow (n := 72) ha hb

theorem or_lt_72 (a b : Nat) (ha : a < 4722366482869645213696) (hb : b < 4722366482869645213696) : a ||| b < 4722366482869645213696 :=
  Nat.or_lt_two_pow (n := 72) ha hb

theorem xor_lt_80 (a b : Nat) (ha : a < 1208925819614629174706176) (hb : b < 1208925819614629174706176) : a ^^^ b < 1208925819614629174706176 :=
  Nat.xor_lt_two_pow (n := 80) ha hb

theorem or_lt_80 (a b : Nat) (ha : a < 1208925819614629174706176) (hb : b < 1208925819614629174706176) : a ||| b < 1208925819614629174706176 :=
  Nat.or_lt_two_pow (n := 80) ha hb

theorem xor_lt_88 (a b : Nat) (ha : a < 309485009821345068724781056) (hb : b < 309485009821345068724781056) : a ^^^ b < 309485009821345068724781056 :=
  Nat.xor_lt_two_pow (n := 88) ha hb

theorem or_lt_88 (a b : Nat) (ha : a < 309485009821345068724781056) (hb : b < 309485009821345068724781056) : a ||| b < 309485009821345068724781056 :=
  Nat.or_lt_two_pow (n := 88) ha hb

theorem xor_lt_96 (a b : Nat) (ha : a < 79228162514264337593543950336) (hb : b < 79228162514264337593543950336) : a ^^^ b < 79228162514264337593543950336 :=
  Nat.xor_lt_two_pow (n := 96) ha hb

theorem or_lt_96 (a b : Nat) (ha : a < 79228162514264337593543950336) (hb : b < 79228162514264337593543950336) : a ||| b < 79228162514264337593543950336 :=
  Nat.or_lt_two_pow (n := 96) ha hb

theorem xor_lt_104 (a b : Nat) (ha : a < 20282409603651670423947251286016) (hb : b < 20282409603651670423947251286016) : a ^^^ b < 20282409603651670423947251286016 :=
  Nat.xor_lt_two_pow (n := 104) ha hb

theorem or_lt_104 (a b : Nat) (ha : a < 20282409603651670423947251286016) (hb : b < 20282409603651670423947251286016) : a ||| b < 20282409603651670423947251286016 :=
  Nat.or_lt_two_pow (n := 104) ha hb

theorem xor_lt_112 (a b : Nat) (ha : a < 5192296858534827628530496329220096) (hb : b < 5192296858534827628530496329220096) : a ^^^ b < 5192296858534827628530496329220096 :=
  Nat.xor_lt_two_pow (n := 112) ha hb

theorem or_lt_112 (a b : Nat) (ha : a < 5192296858534827628530496329220096) (hb : b < 5192296858534827628530496329220096) : a ||| b < 5192296858534827628530496329220096 :=
  Nat.or_lt_two_pow (n := 112) ha hb

theorem xor_lt_120 (a b : Nat) (ha : a < 1329227995784915872903807060280344576) (hb : b < 1329227995784915872903807060280344576) : a ^^^ b < 1329227995784915872903807060280344576 :=
  Nat.xor_lt_two_pow (n := 120) ha hb

theorem or_lt_120 (a b : Nat) (ha : a < 1329227995784915872903807060280344576) (hb : b < 1329227995784915872903807060280344576) : a ||| b < 1329227995784915872903807060280344576 :=
  Nat.or_lt_two_pow (n := 120) ha hb

theorem xor_lt_128 (a b : Nat) (ha : a < 340282366920938463463374607431768211456) (hb : b < 340282366920938463463374607431768211456) : a ^^^ b < 340282366920938463463374607431768211456 :=
  Nat.xor_lt_two_pow (n := 128) ha hb

theorem or_lt_128 (a b : Nat) (ha : a < 340282366920938463463374607431768211456) (hb : b < 340282366920938463463374607431768211456) : a ||| b < 340282366920938463463374607431768211456 :=
  Nat.or_lt_two_pow (n := 128) ha hb

theorem xor_lt_136 (a b : Nat) (ha : a < 87112285931760246646623899502532662132736) (hb : b < 87112285931760246646623899502532662132736) : a ^^^ b < 87112285931760246646623899502532662132736 :=
  Nat.xor_lt_two_pow (n := 136) ha hb

theorem or_lt_136 (a b : Nat) (ha : a < 87112285931760246646623899502532662132736) (hb : b < 87112285931760246646623899502532662132736) : a ||| b < 87112285931760246646623899502532662132736 :=
  Nat.or_lt_two_pow (n := 136) ha hb

theorem xor_lt_144 (a b : Nat) (ha : a < 22300745198530623141535718272648361505980416) (hb : b < 22300745198530623141535718272648361505980416) : a ^^^ b < 22300745198530623141535718272648361505980416 :=
  Nat.xor_lt_two_pow (n := 144) ha hb

theorem or_lt_144 (a b : Nat) (ha : a < 22300745198530623141535718272648361505980416) (hb : b < 22300745198530623141535718272648361505980416) : a ||| b < 22300745198530623141535718272648361505980416 :=
  Nat.or_lt_two_pow (n := 144) ha hb

theorem xor_lt_152 (a b : Nat) (ha : a < 5708990770823839524233143877797980545530986496) (hb : b < 5708990770823839524233143877797980545530986496) : a ^^^ b < 5708990770823839524233143877797980545530986496 :=
  Nat.xor_lt_two_pow (n := 152) ha hb

theorem or_lt_152 (a b : Nat) (ha : a < 5708990770823839524233143877797980545530986496) (hb : b < 5708990770823839524233143877797980545530986496) : a ||| b < 5708990770823839524233143877797980545530986496 :=
  Nat.or_lt_two_pow (n := 152) ha hb

theorem xor_lt_160 (a b : Nat) (ha : a < 1461501637330902918203684832716283019655932542976) (hb : b < 1461501637330902918203684832716283019655932542976) : a ^^^ b < 1461501637330902918203684832716283019655932542976 :=
  Nat.xor_lt_two_pow (n := 160) ha hb

theorem or_lt_160 (a b : Nat) (ha : a < 1461501637330902918203684832716283019655932542976) (hb : b < 1461501637330902918203684832716283019655932542976) : a ||| b < 1461501637330902918203684832716283019655932542976 :=
  Nat.or_lt_two_pow (n := 160) ha hb

theorem xor_lt_168 (a b : Nat) (ha : a < 374144419156711147060143317175368453031918731001856) (hb : b < 374144419156711147060143317175368453031918731001856) : a ^^^ b < 374144419156711147060143317175368453031918731001856 :=
  Nat.xor_lt_two_pow (n := 168) ha hb

theorem or_lt_168 (a b : Nat) (ha : a < 374144419156711147060143317175368453031918731001856) (hb : b < 374144419156711147060143317175368453031918731001856) : a ||| b < 374144419156711147060143317175368453031918731001856 :=
  Nat.or_lt_two_pow (n := 168) ha hb

theorem xor_lt_176 (a b : Nat) (ha : a < 95780971304118053647396689196894323976171195136475136) (hb : b < 95780971304118053647396689196894323976171195136475136) : a ^^^ b < 95780971304118053647396689196894323976171195136475136 :=
  Nat.xor_lt_two_pow (n := 176) ha hb

theorem or_lt_176 (a b : Nat) (ha : a < 95780971304118053647396689196894323976171195136475136) (hb : b < 95780971304118053647396689196894323976171195136475136) : a ||| b < 95780971304118053647396689196894323976171195136475136 :=
  Nat.or_lt_two_pow (n := 176) ha hb

theorem xor_lt_184 (a b : Nat) (ha : a < 24519928653854221733733552434404946937899825954937634816) (hb : b < 24519928653854221733733552434404946937899825954937634816) : a ^^^ b < 24519928653854221733733552434404946937899825954937634816 :=
  Nat.xor_lt_two_pow (n := 184) ha hb

theorem or_lt_184 (a b : Nat) (ha : a < 24519928653854221733733552434404946937899825954937634816) (hb : b < 24519928653854221733733552434404946937899825954937634816) : a ||| b < 24519928653854221733733552434404946937899825954937634816 :=
  Nat.or_lt_two_pow (n := 184) ha hb

theorem xor_lt_192 (a b : Nat) (ha : a < 6277101735386680763835789423207666416102355444464034512896) (hb : b < 6277101735386680763835789423207666416102355444464034512896) : a ^^^ b < 6277101735386680763835789423207666416102355444464034512896 :=
  Nat.xor_lt_two_pow (n := 192) ha hb

theorem or_lt_192 (a b : Nat) (ha : a < 6277101735386680763835789423207666416102355444464034512896) (hb : b < 6277101735386680763835789423207666416102355444464034512896) : a ||| b < 6277101735386680763835789423207666416102355444464034512896 :=
  Nat.or_lt_two_pow (n := 192) ha hb

theorem xor_lt_200 (a b : Nat) (ha : a < 1606938044258990275541962092341162602522202993782792835301376) (hb : b < 1606938044258990275541962092341162602522202993782792835301376) : a ^^^ b < 1606938044258990275541962092341162602522202993782792835301376 :=
  Nat.xor_lt_two_pow (n := 200) ha hb

theorem or_lt_200 (a b : Nat) (ha : a < 1606938044258990275541962092341162602522202993782792835301376) (hb : b < 1606938044258990275541962092341162602522202993782792835301376) : a ||| b < 1606938044258990275541962092341162602522202993782792835301376 :=
  Nat.or_lt_two_pow (n := 200) ha hb

theorem xor_lt_208 (a b : Nat) (ha : a < 411376139330301510538742295639337626245683966408394965837152256) (hb : b < 411376139330301510538742295639337626245683966408394965837152256) : a ^^^ b < 411376139330301510538742295639337626245683966408394965837152256 :=
  Nat.xor_lt_two_pow (n := 208) ha hb

theorem or_lt_208 (a b : Nat) (ha : a < 411376139330301510538742295639337626245683966408394965837152256) (hb : b < 411376139330301510538742295639337626245683966408394965837152256) : a ||| b < 411376139330301510538742295639337626245683966408394965837152256 :=
  Nat.or_lt_two_pow (n := 208) ha hb

theorem xor_lt_216 (a b : Nat) (ha : a < 105312291668557186697918027683670432318895095400549111254310977536) (hb : b < 105312291668557186697918027683670432318895095400549111254310977536) : a ^^^ b < 105312291668557186697918027683670432318895095400549111254310977536 :=
  Nat.xor_lt_two_pow (n := 216) ha hb

theorem or_lt_216 (a b : Nat) (ha : a < 105312291668557186697918027683670432318895095400549111254310977536) (hb : b < 105312291668557186697918027683670432318895095400549111254310977536) : a ||| b < 105312291668557186697918027683670432318895095400549111254310977536 :=
  Nat.or_lt_two_pow (n := 216) ha hb

theorem xor_lt_224 (a b : Nat) (ha : a < 26959946667150639794667015087019630673637144422540572481103610249216) (hb : b < 26959946667150639794667015087019630673637144422540572481103610249216) : a ^^^ b < 26959946667150639794667015087019630673637144422540572481103610249216 :=
  Nat.xor_lt_two_pow (n := 224) ha hb

theorem or_lt_224 (a b : Nat) (ha : a < 26959946667150639794667015087019630673637144422540572481103610249216) (hb : b < 26959946667150639794667015087019630673637144422540572481103610249216) : a ||| b < 26959946667150639794667015087019630673637144422540572481103610249216 :=
  Nat.or_lt_two_pow (n := 224) ha hb

theorem xor_lt_232 (a b : Nat) (ha : a < 6901746346790563787434755862277025452451108972170386555162524223799296) (hb : b < 6901746346790563787434755862277025452451108972170386555162524223799296) : a ^^^ b < 6901746346790563787434755862277025452451108972170386555162524223799296 :=
  Nat.xor_lt_two_pow (n := 232) ha hb

theorem or_lt_232 (a b : Nat) (ha : a < 6901746346790563787434755862277025452451108972170386555162524223799296) (hb : b < 6901746346790563787434755862277025452451108972170386555162524223799296) : a ||| b < 6901746346790563787434755862277025452451108972170386555162524223799296 :=
  Nat.or_lt_two_pow (n := 232) ha hb

theorem xor_lt_240 (a b : Nat) (ha : a < 1766847064778384329583297500742918515827483896875618958121606201292619776) (hb : b < 1766847064778384329583297500742918515827483896875618958121606201292619776) : a ^^^ b < 1766847064778384329583297500742918515827483896875618958121606201292619776 :=
  Nat.xor_lt_two_pow (n := 240) ha hb

theorem or_lt_240 (a b : Nat) (ha : a < 1766847064778384329583297500742918515827483896875618958121606201292619776) (hb : b < 1766847064778384329583297500742918515827483896875618958121606201292619776) : a ||| b < 1766847064778384329583297500742918515827483896875618958121606201292619776 :=
  Nat.or_lt_two_pow (n := 240) ha hb

theorem xor_lt_248 (a b : Nat) (ha : a < 452312848583266388373324160190187140051835877600158453279131187530910662656) (hb : b < 452312848583266388373324160190187140051835877600158453279131187530910662656) : a ^^^ b < 452312848583266388373324160190187140051835877600158453279131187530910662656 :=
  Nat.xor_lt_two_pow (n := 248) ha hb

theorem or_lt_248 (a b : Nat) (ha : a < 452312848583266388373324160190187140051835877600158453279131187530910662656) (hb : b < 452312848583266388373324160190187140051835877600158453279131187530910662656) : a ||| b < 452312848583266388373324160190187140051835877600158453279131187530910662656 :=
  Nat.or_lt_two_pow (n := 248) ha hb

theorem xor_lt_256 (a b : Nat) (ha : a < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (hb : b < 115792089237316195423570985008687907853269984665640564039457584007913129639936) : a ^^^ b < 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  Nat.xor_lt_two_pow (n := 256) ha hb

theorem or_lt_256 (a b : Nat) (ha : a < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (hb : b < 115792089237316195423570985008687907853269984665640564039457584007913129639936) : a ||| b < 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  Nat.or_lt_two_pow (n := 256) ha hb

/-- The bounds of `^^^` and `|||` at each width. -/
def widthLemmas : List Name :=
  [``xor_lt_8, ``or_lt_8, ``xor_lt_16, ``or_lt_16, ``xor_lt_24, ``or_lt_24, ``xor_lt_32, ``or_lt_32, ``xor_lt_40, ``or_lt_40, ``xor_lt_48, ``or_lt_48, ``xor_lt_56, ``or_lt_56, ``xor_lt_64, ``or_lt_64, ``xor_lt_72, ``or_lt_72, ``xor_lt_80, ``or_lt_80, ``xor_lt_88, ``or_lt_88, ``xor_lt_96, ``or_lt_96, ``xor_lt_104, ``or_lt_104, ``xor_lt_112, ``or_lt_112, ``xor_lt_120, ``or_lt_120, ``xor_lt_128, ``or_lt_128, ``xor_lt_136, ``or_lt_136, ``xor_lt_144, ``or_lt_144, ``xor_lt_152, ``or_lt_152, ``xor_lt_160, ``or_lt_160, ``xor_lt_168, ``or_lt_168, ``xor_lt_176, ``or_lt_176, ``xor_lt_184, ``or_lt_184, ``xor_lt_192, ``or_lt_192, ``xor_lt_200, ``or_lt_200, ``xor_lt_208, ``or_lt_208, ``xor_lt_216, ``or_lt_216, ``xor_lt_224, ``or_lt_224, ``xor_lt_232, ``or_lt_232, ``xor_lt_240, ``or_lt_240, ``xor_lt_248, ``or_lt_248, ``xor_lt_256, ``or_lt_256]

/-- The word lemmas the evaluator always uses. -/
def wordLemmas : List Name :=
  [``uint256_size, ``wordModulus_eq, ``toNat_mod_word, ``toNat_lt_word, ``not_word_le_toNat,
   ``mod_word_lt, ``not_word_le_mod, ``ite_mod_word, ``mod_mod_of_le, ``mod_lt_of_le,
   ``and_lt_of_lt, ``Nat.mod_eq_of_lt, ``Nat.not_le_of_lt] ++ widthLemmas

/-! ## The tactics -/

/-- The simp set of the given lemmas and the monad and word lemmas. Given lemmas come at
high priority, so that they rewrite before a definition they mention is unfolded. -/
def baseTheorems (ts : Array Syntax) : TacticM SimpTheorems := do (← getMainGoal).withContext do
  let mut thms ← getSimpTheorems
  for n in monadLemmas ++ wordLemmas do
    thms ← thms.addConst n
  for t in ts do
    if t.isIdent then
      if let some n ← (try some <$> realizeGlobalConstNoOverload t catch _ => pure none) then
        if ((← getEnv).find? n).any ConstantInfo.isDefinition then
          thms ← thms.addDeclToUnfold n
          continue
    let e ← elabTerm t none
    thms ← thms.add (.stx (← mkFreshId) t) #[] e (prio := 2000)
  return thms

/-- Runs the evaluator on `g` to a fixed point; `none` when it closes the goal. -/
def evalGoal (base : SimpTheorems) (g : MVarId) : TacticM (Option MVarId) := do
  let mut thms := base
  let mut done : NameSet := {}
  let mut g := g
  for _ in [0:400] do
    let names ← unfoldableIn (← instantiateMVars (← g.getType))
    for n in names.toList do
      unless done.contains n do
        done := done.insert n
        thms ← tryCatchRuntimeEx (thms.addDeclToUnfold n) (fun _ => pure thms)
    let thms' := thms
    let (r, _) ← g.withContext do
      let mut thmsH := thms'
      for h in (← getLCtx) do
        if !h.isImplementationDetail && (← isProp h.type) then
          thmsH ← thmsH.add (.fvar h.fvarId) #[] h.toExpr
      let ctx ← Simp.mkContext
        (config := { decide := true, maxSteps := 100000000, maxDischargeDepth := 4 })
        (simpTheorems := #[thmsH]) (congrTheorems := ← getSimpCongrTheorems)
      try simpGoal g ctx (simprocs := #[← Simp.getSimprocs])
      catch _ => pure (some (#[], g), {})
    match r with
    | none => return none
    | some (_, g') =>
      if g' == g then return some g
      g := g'
  return some g

/-- Symbolic evaluation of SolidCore's interpreter, without splitting. -/
syntax "src_eval" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| src_eval $[[$ts,*]]?) => do
    let base ← baseTheorems (ts.map (·.getElems.map (·.raw)) |>.getD #[])
    match ← evalGoal base (← getMainGoal) with
    | none => replaceMainGoal []
    | some g => replaceMainGoal [g]

/-- The condition of an `if` in `e` that mentions no bound variable, if any, innermost
first. -/
partial def closedCond? (e : Expr) : Option Expr :=
  if (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && !e.appFn!.appFn!.appFn!.appArg!.hasLooseBVars then
    let c := e.appFn!.appFn!.appFn!.appArg!
    -- An `if` inside the condition comes first, so that each split is on an atomic fact.
    (closedCond? c).orElse fun _ => some c
  else
    match e with
    | .app f a => (closedCond? f).orElse fun _ => closedCond? a
    | .lam _ t b _ | .forallE _ t b _ => (closedCond? t).orElse fun _ => closedCond? b
    | .letE _ t v b _ => ((closedCond? t).orElse fun _ => closedCond? v).orElse fun _ => closedCond? b
    | .mdata _ b => closedCond? b
    | .proj _ _ b => closedCond? b
    | _ => none

/-- Evaluates `g`, and on each branch that no longer simplifies splits on the condition of an
`if` it still holds (by `by_cases`), or else on its first `match` (by `split`), up to
`depth` splits deep. Returns the goals left. -/
partial def symexGoal (base : SimpTheorems) (depth : Nat) (g : MVarId) :
    TacticM (List MVarId) := do
  match ← evalGoal base g with
  | none => return []
  | some g =>
    if depth = 0 then return [g]
    let ty ← g.withContext do instantiateMVars (← g.getType)
    let split? ← try
        some <$> (do
          setGoals [g]
          match closedCond? ty with
          | some c =>
            let hc ← g.withContext do Term.exprToSyntax c
            evalTactic (← `(tactic| by_cases hpath : $hc))
          | none => evalTactic (← `(tactic| split))
          getGoals)
      catch _ => pure none
    match split? with
    | none => return [g]
    | some gs =>
      let mut out := []
      for g' in gs do
        -- A branch whose path conditions contradict each other by linear arithmetic is closed.
        let closed ← try
            setGoals [g']
            evalTactic (← `(tactic| (exfalso; omega)))
            pure true
          catch _ => pure false
        unless closed do
          out := out ++ (← symexGoal base (depth - 1) g')
      return out

/-- Symbolic evaluation of SolidCore's interpreter with path splitting. -/
syntax "src_symex" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| src_symex $[[$ts,*]]?) => do
    let base ← baseTheorems (ts.map (·.getElems.map (·.raw)) |>.getD #[])
    let rest := (← getGoals).drop 1
    let gs ← symexGoal base 16 (← getMainGoal)
    setGoals (gs ++ rest)

end SolidCore.Refinement.Wide
