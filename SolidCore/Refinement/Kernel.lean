import Lean

/-!
# Kernel evaluation through well-founded recursion

The kernel cannot unfold a definition by well-founded recursion on anything but a
`Nat` measure: the elaborator wraps its well-foundedness proof in `Lean.opaqueId`, so
`WellFounded.fix` never reduces. `kernel_clone c` lets the kernel evaluate a closed
term `c` anyway. For every definition `d` that `c` reaches and that reaches such a
fixpoint, it adds a copy `d.kclone` that calls the copies instead, and replaces each
fixpoint `fun ps => WellFounded.fix wf F` by `fun ps => unroll F (d ps) depth`:
`depth` unfoldings of the functional, over the original fixpoint below. Evaluation that
recurses less than `depth` deep never reaches the original, so the kernel evaluates
the copy. With each copy comes `d.kclone_eq : d = d.kclone`, by `fix_eq_unroll` and
congruence, so a fact the kernel decides of `c.kclone` holds of `c`.

Copies are shared: a definition already copied in an imported module is reused.
-/

namespace SolidCore.Refinement.Kernel

universe u v

/-- `n` unfoldings of the functional `F` of a well-founded fixpoint, over `g` below. -/
noncomputable def unroll {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
    (F : ∀ x, (∀ y, r y x → C y) → C x) (g : ∀ x, C x) (n : Nat) : ∀ x, C x :=
  Nat.rec (motive := fun _ => ∀ x, C x) g (fun _ ih x => F x (fun y _ => ih y)) n

/-- A well-founded fixpoint is its own `n`-fold unfolding. -/
theorem fix_eq_unroll {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
    (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (n : Nat) :
    WellFounded.fix hwf F = unroll F (WellFounded.fix hwf F) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    show WellFounded.fix hwf F x = F x (fun y _ => unroll F (WellFounded.fix hwf F) n y)
    rw [← ih]
    exact WellFounded.fix_eq hwf F x

open Lean Meta Elab Command

/-- The unfolding depth of every copied fixpoint. -/
def depth : Nat := 1000000

/-- The body under a term's leading lambdas. -/
def lamBody : Expr → Expr
  | .lam _ _ b _ => lamBody b
  | e => e

/-- Whether a definition's value is a well-founded fixpoint under lambdas. -/
def isWFFix (v : Expr) : Bool :=
  (lamBody v).getAppFn.isConstOf ``WellFounded.fix

/-- The copy's name of a constant at universe levels `ls`. -/
def cloneName (c : Name) (ls : List Level) : Name :=
  if ls.isEmpty then c ++ `kclone
  else c ++ Name.mkSimple ("kclone_" ++ String.intercalate "_" (ls.map (toString ·.normalize)))

/-- The name of the copy's equation. -/
def eqName (clone : Name) : Name := clone ++ `eq

structure CloneState where
  /-- The prefix of the names of new copies: empty for shared copies, a module's own
  namespace otherwise, so that two modules never add the same name. -/
  pre : Name := .anonymous
  /-- Affected instances, by copy name: `some` copy or `none` when unaffected. -/
  done : Std.HashMap Name (Option Name) := {}
  added : Nat := 0

abbrev CloneM := StateRefT CloneState MetaM

/-- The instance `c.{ls}`'s definition, its levels instantiated. -/
def instDefn? (c : Name) (ls : List Level) : MetaM (Option (Expr × Expr)) := do
  match (← getEnv).find? c with
  | some (.defnInfo d) =>
    if d.safety != .safe then return none
    return some (d.type.instantiateLevelParams d.levelParams ls,
      d.value.instantiateLevelParams d.levelParams ls)
  | _ => return none

/-- The distinct constant instances `e` mentions. -/
partial def constInsts (e : Expr) : Array Expr :=
  (go e).run ({}, #[]) |>.2.2
where
  go (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
    if (← get).1.contains e then return
    modify fun (s, a) => (s.insert e, a)
    match e with
    | .const .. => modify fun (s, a) => (s, if a.contains e then a else a.push e)
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()

/-- Replace the constant instances `subst` maps, keeping the term's sharing: a memo on
every subterm, where `Expr.replace`'s bounded cache would unshare a large term. -/
partial def replaceConsts (e : Expr) (subst : Std.HashMap Expr Expr) : Expr :=
  (go e).run' {}
where
  go (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
    if let some r := (← get)[e]? then return r
    let r ← match e with
      | .const .. => pure (subst[e]?.getD e)
      | .app f a => return e.updateApp! (← go f) (← go a)
      | .lam _ t b _ => return e.updateLambdaE! (← go t) (← go b)
      | .forallE _ t b _ => return e.updateForallE! (← go t) (← go b)
      | .letE _ t v b _ => return e.updateLetE! (← go t) (← go v) (← go b)
      | .mdata _ b => return e.updateMData! (← go b)
      | .proj _ _ b => return e.updateProj! (← go b)
      | _ => pure e
    modify (·.insert e r)
    return r

/-- Trace the copying on stderr. -/
def debugClone : Bool := false

/-- The leading lambdas' binders (name, domain, info) and the body under them. -/
def lamBinders : Expr → Array (Name × Expr × BinderInfo) → Array (Name × Expr × BinderInfo) × Expr
  | .lam n t b bi, acc => lamBinders b (acc.push (n, t, bi))
  | e, acc => (acc, e)

/-- Wrap `body` in lambdas with binders `bs`. -/
def wrapLams (bs : Array (Name × Expr × BinderInfo)) (body : Expr) : Expr :=
  bs.foldr (fun (n, t, bi) e => .lam n t e bi) body

/-- `hs[i] : as[i] = bs[i]` and `M : types → type` give `M as = M bs`. Built by hand,
not by `mkCongr`, which would infer the type of `M`. -/
def congrN (M : Expr) (types : Array Expr) (type : Expr) (as bs hs : Array Expr) :
    MetaM Expr := do
  -- `rest[j]`: the type of `M` applied to its first `j` arguments.
  let mut rest := #[type]
  for t in types.reverse do
    rest := rest.push (← mkArrow t rest.back!)
  rest := rest.reverse
  let mut h := mkApp2 (mkConst ``Eq.refl [← getLevel rest[0]!]) rest[0]! M
  let mut f1 := M
  let mut f2 := M
  for j in [:hs.size] do
    let α := types[j]!
    let β := rest[j + 1]!
    h := mkAppN (mkConst ``congr [← getLevel α, ← getLevel β])
      #[α, β, f1, f2, as[j]!, bs[j]!, h, hs[j]!]
    f1 := mkApp f1 as[j]!
    f2 := mkApp f2 bs[j]!
  return h

/-- The pieces of a fixpoint body `WellFounded.fix α C r hwf F es` (at most one `e`). -/
def fixParts (body : Expr) : MetaM (List Level × Array Expr × Array Expr) := do
  let args := body.getAppArgs
  let extra := args[5:].toArray
  if extra.size > 1 then throwError "kernel_clone: a fixpoint applied to {extra.size} arguments"
  return (body.getAppFn.constLevels!, args[:5].toArray, extra)

/-- `unroll F' (WellFounded.fix α C r hwf F) depth es`, from the original's pieces and
the copy's functional `F'`. -/
def unrolled (lvls : List Level) (args extra : Array Expr) (F' : Expr) : Expr :=
  let fixFn := mkAppN (mkConst ``WellFounded.fix lvls) args
  mkAppN (mkAppN (mkConst ``unroll lvls) #[args[0]!, args[1]!, args[2]!, F', fixFn, mkNatLit depth])
    extra

/-- For `value = fun ps => WellFounded.fix α C r hwf F es` of type `type`, a proof of
`value = fun ps => unroll F (WellFounded.fix α C r hwf F) depth es`, built on the
value's own subterms (with loose bound variables) so that `F` is shared, not copied. -/
def unrollProof (value type : Expr) : MetaM Expr := do
  let (bs, body) := lamBinders value #[]
  let (lvls, args, extra) ← fixParts body
  let fixFn := mkAppN (mkConst ``WellFounded.fix lvls) args
  let n := mkNatLit depth
  let unr := mkAppN (mkConst ``unroll lvls) #[args[0]!, args[1]!, args[2]!, args[4]!, fixFn, n]
  let mut pf := mkAppN (mkConst ``fix_eq_unroll lvls) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, n]
  let mut lhs := mkAppN fixFn extra
  let mut rhs := mkAppN unr extra
  -- `B`: the type of `lhs`.
  let mut B := match extra[0]? with
    | some e => mkApp args[1]! e
    | none => .forallE `x args[0]! (mkApp (args[1]!.liftLooseBVars 0 1) (.bvar 0)) .default
  for e in extra do
    pf := mkAppN (mkConst ``congrFun lvls) #[args[0]!, args[1]!, fixFn, unr, pf, e]
  -- Levels of the domains and of `B` under them, on free variables.
  let k := bs.size
  let levels ← forallBoundedTelescope type (some k) fun ps _ => do
    let mut out := #[]
    let mut Bi := B
    for i' in [:k] do
      let i := k - 1 - i'
      let D := bs[i]!.2.1.instantiateRev ps[:i]
      out := out.push (← getLevel D, ← getLevel (Bi.instantiateRev ps[:i + 1]))
      Bi := .forallE bs[i]!.1 bs[i]!.2.1 Bi bs[i]!.2.2
    return out
  for i' in [:k] do
    let i := k - 1 - i'
    let (nm, D, bi) := bs[i]!
    let (u, v) := levels[i']!
    let f := Expr.lam nm D lhs bi
    let g := Expr.lam nm D rhs bi
    pf := mkAppN (mkConst ``funext [u, v]) #[D, .lam nm D B bi, f, g, .lam nm D pf bi]
    B := .forallE nm D B bi
    lhs := f
    rhs := g
  return pf

mutual

/-- The copy of the instance `x` (a constant), when it reaches a well-founded fixpoint. -/
partial def cloneInst (x : Expr) : CloneM (Option Expr) := do
  let c := x.constName!
  let ls := x.constLevels!
  let shared := cloneName c ls
  let name := (← get).pre ++ shared
  if let some r := (← get).done[name]? then return r.map (mkConst ·)
  for n in [shared, name] do
    if (← getEnv).contains n then
      modify fun s => { s with done := s.done.insert name (some n) }
      return some (mkConst n)
  -- Constants are acyclic, so this placeholder is never read for `x` itself.
  modify fun s => { s with done := s.done.insert name none }
  let some (type, value) ← instDefn? c ls | return none
  let target := isWFFix value
  let mut as := #[]
  let mut bs := #[]
  let mut others := #[]
  for y in constInsts value do
    if let some b ← cloneInst y then
      as := as.push y
      bs := bs.push b
    else others := others.push y
  if !target && as.isEmpty then return none
  -- Unaffected constants whose types mention affected ones (the proofs of a
  -- well-founded definition's decreasing obligations) are cast along the equations.
  let mut casts := #[]
  for y in others do
    let ty ← inferType y
    let mut uses := #[]
    for t in constInsts ty do
      if let some b ← cloneInst t then
        uses := uses.push t
        unless as.contains t do
          as := as.push t
          bs := bs.push b
    unless uses.isEmpty do casts := casts.push y
  build x name type value target as bs casts
  modify fun s => { s with done := s.done.insert name (some name), added := s.added + 1 }
  return some (mkConst name)

/-- Add `name`, the copy of the instance `x` with value `value`, and its equation
`x = name`. The copy is `name.gen b₁ h₁ … bₙ hₙ`, where `name.gen z₁ e₁ … zₙ eₙ`
(`eᵢ : aᵢ = zᵢ`) is the value (for a fixpoint, its unfolding) with each affected
constant `aᵢ` replaced by `zᵢ`, and each constant of `casts` cast along the `eᵢ` its
type mentions; `hᵢ : aᵢ = bᵢ` is the equation of `aᵢ`'s copy `bᵢ`. The large value is
copied once, and the equation follows by `Eq.rec` on each `hᵢ`. -/
partial def build (x : Expr) (name : Name) (type value : Expr) (target : Bool)
    (as bs casts : Array Expr) : CloneM Unit := do
  if debugClone then
    let st ← IO.FS.readFile "/proc/self/status"
    let rss := (st.splitOn "
").filter (·.startsWith "VmRSS") |>.headD ""
    IO.eprintln s!"build {name} ({as.size} copies used, {casts.size} casts) {rss}"
  let hs := bs.map fun b => mkConst (eqName b.constName!)
  let types ← as.mapM fun a => (inferType a : MetaM Expr)
  let lvls ← types.mapM fun t => (getLevel t : MetaM Level)
  let zs ← as.mapM fun _ => do return mkFVar (← mkFreshFVarId)
  let es ← as.mapM fun _ => do return mkFVar (← mkFreshFVarId)
  let eqT (j : Nat) (b : Expr) := mkApp3 (mkConst ``Eq [lvls[j]!]) types[j]! as[j]! b
  let rfl (j : Nat) := mkApp2 (mkConst ``Eq.refl [lvls[j]!]) types[j]! as[j]!
  let mut subst : Std.HashMap Expr Expr :=
    (as.zip zs).foldl (init := {}) fun m (a, z) => m.insert a z
  -- `c` cast along `e_j` for each `a_j` its type mentions, in order.
  for c in casts do
    let ty ← inferType c
    let u ← getLevel ty
    let mut term := c
    let mut cur := ty
    let present := constInsts ty
    for j in [:as.size] do
      unless present.contains as[j]! do continue
      let y ← mkFreshFVarId
      let next := replaceConsts cur (({} : Std.HashMap Expr Expr).insert as[j]! (mkFVar y))
      let motive := Expr.lam `y types[j]! (.lam `h (eqT j (.bvar 0)) (next.abstract #[mkFVar y] |>.liftLooseBVars 0 1) .default) .default
      term := mkAppN (mkConst ``Eq.rec [u, lvls[j]!]) #[types[j]!, as[j]!, motive, term, zs[j]!, es[j]!]
      cur := replaceConsts cur (({} : Std.HashMap Expr Expr).insert as[j]! zs[j]!)
    subst := subst.insert c term
  let body ← if target then do
      -- `fun ps => unroll F[zs] (fix α C r hwf F) depth es`
      let (bnds, fixBody) := lamBinders value #[]
      let (lvl, args, extra) ← fixParts fixBody
      let bndsZ := bnds.map fun (n, t, bi) => (n, replaceConsts t subst, bi)
      pure (wrapLams bndsZ (unrolled lvl args extra (replaceConsts args[4]! subst)))
    else pure (replaceConsts value subst)
  -- Binders `z_j : A_j`, `e_j : a_j = z_j`.
  let xs := (zs.zip es).foldl (init := #[]) fun acc (z, e) => acc.push z |>.push e
  let bTypes := (Array.range as.size).foldl (init := #[]) fun acc j =>
    acc.push types[j]! |>.push (eqT j zs[j]!)
  let lamOver (e : Expr) (mk : Name → Expr → Expr → Expr) : Expr := Id.run do
    let mut r := e.abstract xs
    for i' in [:xs.size] do
      let i := xs.size - 1 - i'
      r := mk (Name.mkSimple s!"x{i}") (bTypes[i]!.abstractRange i xs) r
    return r
  let gen := lamOver body fun n t b => .lam n t b .default
  let genType := lamOver type fun n t b => .forallE n t b .default
  let genName := name ++ `gen
  let genApp (args : Array Expr) := mkAppN (mkConst genName) args
  try
    let env ← getEnv
    let genDefn : DefinitionVal :=
      { name := genName, levelParams := [], type := genType, value := gen,
        hints := .regular (getMaxHeight env gen + 1), safety := .safe }
    addDecl (.defnDecl genDefn)
    let cloneArgs := (bs.zip hs).foldl (init := #[]) fun acc (b, h) => acc.push b |>.push h
    let cloneDefn : DefinitionVal :=
      { name := name, levelParams := [], type := type, value := genApp cloneArgs,
        hints := .regular (getMaxHeight env gen + 2), safety := .safe }
    addDecl (.defnDecl cloneDefn)
    -- `x = gen a₁ rfl … aₙ rfl`, by unfolding (and, for a fixpoint, `fix_eq_unroll`).
    let w ← getLevel type
    let pf0 ← if target then unrollProof value type
      else pure (mkApp2 (mkConst ``Eq.refl [w]) type x)
    let mut pf := pf0
    -- Then rewrite the `j`-th pair from `a_j, rfl` to `b_j, h_j`.
    for j in [:as.size] do
      let pre := (Array.range j).foldl (init := #[]) fun acc i => acc.push bs[i]! |>.push hs[i]!
      let post := (Array.range (as.size - j - 1)).foldl (init := #[]) fun acc i =>
        acc.push as[j + 1 + i]! |>.push (rfl (j + 1 + i))
      let motive := Expr.lam `y types[j]! (.lam `h (eqT j (.bvar 0))
        (mkApp3 (mkConst ``Eq [w]) type x (genApp (pre ++ #[.bvar 1, .bvar 0] ++ post))) .default) .default
      pf := mkAppN (mkConst ``Eq.rec [Level.zero, lvls[j]!]) #[types[j]!, as[j]!, motive, pf, bs[j]!, hs[j]!]
    let eqType := mkApp3 (mkConst ``Eq [w]) type x (mkConst name)
    let thm : TheoremVal := { name := eqName name, levelParams := [], type := eqType, value := pf }
    addDecl (.thmDecl thm)
  catch e =>
    throwError "kernel_clone: copying {x} failed: {e.toMessageData}"

end

/-- The copy of the closed definition `c` and its equation, the names of new copies
prefixed by `pre`. -/
def cloneRoot (c : Name) (pre : Name) : MetaM (Option (Expr × Nat)) := do
  let (r, s) ← (cloneInst (mkConst c)).run { pre := pre }
  return r.map (·, s.added)

/-- `kernel_clone c` adds the shared copy `c.kclone` of the closed definition `c`,
with `c.kclone.eq : c = c.kclone`, and the copies it needs. -/
elab "kernel_clone " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM do
    let t0 ← IO.monoMsNow
    let r ← cloneRoot c .anonymous
    let t1 ← IO.monoMsNow
    match r with
    | some (_, n) => logInfo m!"kernel_clone {c}: {n} copies in {t1 - t0} ms"
    | none => logInfo m!"kernel_clone {c}: nothing to copy"

/-- `kernel_decide h c` proves `h : c = true` for a closed `c : Bool` in the kernel:
it copies `c` (new copies under the current namespace's `kernel`), and the kernel checks
`c = c'` by the copies' equations and `c' = true` by evaluating the copy `c'`. -/
elab "kernel_decide " h:ident ppSpace id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let ns ← getCurrNamespace
  let thmName := ns ++ h.getId
  liftTermElabM do
    let lhs := mkConst c
    let goal := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
    let rfl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let value ← match ← cloneRoot c (ns ++ `kernel) with
      | some (k, _) =>
        let eq := mkConst (eqName k.constName!)
        pure (mkAppN (mkConst ``Eq.trans [1]) #[mkConst ``Bool, lhs, k, mkConst ``Bool.true, eq, rfl])
      | none => pure rfl
    let t0 ← IO.monoMsNow
    let thm : TheoremVal := { name := thmName, levelParams := [], type := goal, value := value }
    withOptions (Elab.async.set · false) <| addDecl (.thmDecl thm)
    let t1 ← IO.monoMsNow
    if debugClone then IO.eprintln s!"kernel_decide {thmName}: kernel check {t1 - t0} ms"

end SolidCore.Refinement.Kernel
