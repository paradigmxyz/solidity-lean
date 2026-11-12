import SolidCore.Refinement.Kernel

/-!
# Kernel equality of a closed term with a value

`kernel_rfl h c v` proves `h : c = v` for a closed definition `c` and a closed term `v`
of its type: it copies `c` (`kernel_clone`, new copies under the current namespace's
`kernel`), and the kernel checks `c = c'` by the copies' equations and `c' = v` by
definitional unfolding of the copy `c'`, as `kernel_decide` checks `c' = true`.

This is how a corpus module learns that SolidCore's checked core of a contract is the
literal it printed, without a decision procedure for equality of cores: the source
syntax (`SolidCore.Solidity.Source.Expr`, `Stmt` and the rest) is nested inductive, so
Lean 4.35 derives no `DecidableEq` for it, and a `match` on the whole literal costs
gigabytes to compile and split. The kernel's own conversion check is the comparison.

`kernel_rfl h c v using e₁ … eₙ`, with `eᵢ : aᵢ = bᵢ` for constants `aᵢ` and `bᵢ`, makes
the copies call `bᵢ` where the originals call `aᵢ`: every definition `c` reaches that
reaches some `aᵢ` gets a copy of its own, named under `kernel.using_e₁_…` and shared by
the module's checks with the same `eᵢ`, with its equation by congruence along the `eᵢ`;
the rest are the shared copies. This is how the kernel skips a costly subcomputation it
checked once, in a declaration of its own: SolidCore's type checker computes each
external function's selector by Keccak-256, whose kernel evaluation costs about 400 MB
a hash, so a module replaces `ABI.selectorFromSignature` by a table of its contract's
selectors, each proved by `kernel_rfl` alone.
-/

namespace SolidCore.Refinement.Kernel

open Lean Meta Elab Command

/-- The state of copying under replacements. -/
structure SubstState where
  /-- The prefix of the names of the copies that reach a replaced constant. -/
  pre : Name
  /-- The prefix of the current module's own copies (`kernel_decide`'s and
  `kernel_rfl`'s), which a copy that reaches no replaced constant may reuse. -/
  modPre : Name
  /-- Replaced constants `aᵢ` and their replacements `bᵢ`, with `bᵢ.eq : aᵢ = bᵢ`. -/
  subst : Std.HashMap Name Name
  /-- Copies, by shared copy name: the copy and whether it reaches a replaced constant. -/
  done : Std.HashMap Name (Option (Expr × Bool)) := {}
  added : Nat := 0

/-- The copy of the instance `x` and whether it reaches a replaced constant: `x`'s
replacement, an existing copy (a shared one only when `x` reaches no replaced
constant), else a new copy. -/
partial def cloneSubst (x : Expr) : StateRefT SubstState MetaM (Option (Expr × Bool)) := do
  let c := x.constName!
  let ls := x.constLevels!
  if let some b := (← get).subst[c]? then return some (mkConst b, true)
  let shared := cloneName c ls
  if let some r := (← get).done[shared]? then return r
  -- Constants are acyclic, so this placeholder is never read for x itself.
  modify fun s => { s with done := s.done.insert shared none }
  let some (type, value) ← instDefn? c ls | return none
  let target := isWFFix value
  let mut as := #[]
  let mut bs := #[]
  let mut others := #[]
  let mut tainted := false
  for y in constInsts value do
    if let some (b, t) ← cloneSubst y then
      as := as.push y
      bs := bs.push b
      tainted := tainted || t
    else others := others.push y
  let mut casts := #[]
  for y in others do
    let ty ← inferType y
    let mut uses := false
    for t in constInsts ty do
      if let some (b, tt) ← cloneSubst t then
        uses := true
        tainted := tainted || tt
        unless as.contains t do
          as := as.push t
          bs := bs.push b
    if uses then casts := casts.push y
  if !target && as.isEmpty then return none
  let s ← get
  let mut r : Option Expr := none
  let names := if tainted then [s.pre ++ shared] else [shared, s.modPre ++ shared, s.pre ++ shared]
  for n in names do
    if r.isNone && (← getEnv).contains n then r := some (mkConst n)
  let e ← match r with
    | some e => pure e
    | none => do
      let name := s.pre ++ shared
      (build x name type value target as bs casts).run' { pre := s.pre }
      modify fun s => { s with added := s.added + 1 }
      pure (mkConst name)
  modify fun s => { s with done := s.done.insert shared (some (e, tainted)) }
  return some (e, tainted)

/-- The copy of the closed definition `c` under the replacements `eqs` (theorems
`aᵢ = bᵢ`), new copies prefixed by `pre`: each `aᵢ` is replaced by `pre ++ bᵢ`, a
definition of `bᵢ` whose equation `(pre ++ bᵢ).eq : aᵢ = pre ++ bᵢ` is `eᵢ`. -/
def cloneRootSubst (c : Name) (pre modPre : Name) (eqs : Array Name) :
    MetaM (Option (Expr × Nat)) := do
  let mut subst : Std.HashMap Name Name := {}
  for e in eqs do
    let some info := (← getEnv).find? e | throwError "kernel_rfl: unknown {e}"
    let some (ty, a, b) := info.type.eq? |
      throwError "kernel_rfl: {e} is not an equation"
    unless a.isConst && b.isConst && a.constLevels!.isEmpty && b.constLevels!.isEmpty do
      throwError "kernel_rfl: {e} does not equate two constants"
    let rep := pre ++ b.constName!
    subst := subst.insert a.constName! rep
    let env ← getEnv
    if env.contains rep then continue
    let defn : DefinitionVal :=
      { name := rep, levelParams := [], type := ty, value := b,
        hints := .regular (getMaxHeight env b + 1), safety := .safe }
    addDecl (.defnDecl defn)
    let u ← getLevel ty
    let thm : TheoremVal :=
      { name := eqName rep, levelParams := [],
        type := mkApp3 (mkConst ``Eq [u]) ty a (mkConst rep), value := mkConst e }
    addDecl (.thmDecl thm)
  let (r, s) ← (cloneSubst (mkConst c)).run { pre := pre, modPre := modPre, subst := subst }
  return r.map fun (e, _) => (e, s.added)

/-- The identifiers of a piece of syntax, in order. -/
partial def identsOf (stx : Syntax) : Array Syntax :=
  if stx.isIdent then #[stx] else stx.getArgs.foldl (fun acc s => acc ++ identsOf s) #[]

/-- `kernel_rfl h c v` proves `h : c = v` in the kernel for a closed definition `c` and
a closed term `v` of its type; `kernel_rfl h c v using e₁ … eₙ` with its copies calling
`bᵢ` for `aᵢ`, where `eᵢ : aᵢ = bᵢ`. -/
syntax (name := kernelRflCmd) "kernel_rfl " ident ppSpace ident ppSpace term:max
  (" using" (ppSpace ident)+)? : command

@[command_elab kernelRflCmd, inherit_doc kernelRflCmd]
def elabKernelRfl : CommandElab := fun stx => do
  let h : Ident := ⟨stx[1]⟩
  let id : Ident := ⟨stx[2]⟩
  let v : Term := ⟨stx[3]⟩
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let eqNames ← liftCoreM <| (identsOf stx[4]).mapM fun e =>
    realizeGlobalConstNoOverloadWithInfo e
  let ns ← getCurrNamespace
  let thmName := ns ++ h.getId
  liftTermElabM do
    let lhs := mkConst c
    let ty ← inferType lhs
    let rhs ← Term.elabTermEnsuringType v ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let rhs ← instantiateMVars rhs
    if rhs.hasMVar || rhs.hasFVar then throwError "kernel_rfl: {rhs} is not closed"
    let u ← getLevel ty
    let goal := mkApp3 (mkConst ``Eq [u]) ty lhs rhs
    let rfl := mkApp2 (mkConst ``Eq.refl [u]) ty rhs
    let t0 ← IO.monoMsNow
    let copy ← if eqNames.isEmpty then cloneRoot c (ns ++ `kernel)
      else
        let tag := String.intercalate "_" (eqNames.toList.map fun e =>
          e.components.getLast!.toString (escape := false))
        cloneRootSubst c (ns ++ `kernel ++ Name.mkSimple ("using_" ++ tag)) (ns ++ `kernel) eqNames
    let value := match copy with
      | some (k, _) =>
        let eq := mkConst (eqName k.constName!)
        mkAppN (mkConst ``Eq.trans [u]) #[ty, lhs, k, rhs, eq, rfl]
      | none => rfl
    let t1 ← IO.monoMsNow
    let thm : TheoremVal := { name := thmName, levelParams := [], type := goal, value := value }
    withOptions (Elab.async.set · false) <| addDecl (.thmDecl thm)
    let t2 ← IO.monoMsNow
    if debugClone then
      IO.eprintln s!"kernel_rfl {thmName}: {copy.map (·.2) |>.getD 0} copies in {t1 - t0} ms, kernel check {t2 - t1} ms"

end SolidCore.Refinement.Kernel
