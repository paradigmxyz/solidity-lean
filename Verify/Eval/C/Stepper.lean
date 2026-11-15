import Verify.Eval.C.Rules
import Lean

/-!
# Lane C: a SymM stepper over the fused rules

`evm_sym [ls]` proves a goal `Spec .fusaka (At (NatCode.ofNat n size) msg pc stack mem gas st ss rd) Q`
or `Hoare .fusaka (At ..) (At ..)` by applying one precompiled `Sym.BackwardRule` per opcode
(the fused rules of `Rules.lean`), chosen by the byte at the program counter, which the stepper reads
off the literal code number. The byte read only selects the rule: the rule's own premises (the byte,
`pc < size`, the PUSH data, gas, stack room, jump destination) are proved, by `Sym.simp` ground
evaluation, an assumption, a kernel-evaluated `walk ... = true` for jump destinations, or `grind`.

Between steps `Sym.simp` (ground evaluation, `simpControl` for `ite`, and a few rewrite rules)
normalizes the frame; its persistent cache is threaded through the whole run, so subterms that do not
change (the code, the message, the postcondition, words already on the stack) hit the cache.

At a JUMPI the stepper takes one branch only when a premise decides the condition (ground evaluation
or a hypothesis); otherwise it applies `step_jumpi_split` and keeps both continuations, each with its
path condition. A branch is closed as infeasible only by a proof: the E-graph finding the new path
condition inconsistent, `grind` on `False`, or `bv_omega` on `False`.

Proof state: one `Lean.Meta.Grind.Goal` is made at the root (`mkGoal` + `internalizeAll` of the
theorem's hypotheses); `Goal.apply` children inherit it; at a split each child introduces and
internalizes only its own path condition, so sibling facts never meet. With
`verify.eval.c.fresh = true` the stepper instead builds a fresh goal (`mkGoal` + `internalizeAll` of
the whole context) every time it needs grind state: the comparison of experiment 1.
-/

open Lean Meta Elab Tactic

namespace Verify.Eval.C.Stepper

open Lean.Meta.Sym (BackwardRule mkBackwardRuleFromDecl)

register_option verify.eval.c.fresh : Bool := {
  defValue := false
  descr := "lane C stepper: fresh grind goal per child instead of the threaded branch-local goal" }
register_option verify.eval.c.eager : Bool := {
  defValue := false
  descr := "lane C stepper: try grind for infeasibility on every split child" }
register_option verify.eval.c.shareCache : Bool := {
  defValue := true
  descr := "lane C stepper: thread the Sym.simp persistent cache across steps" }
register_option verify.eval.c.condRewrite : Bool := {
  defValue := false
  descr := "lane C stepper: conditional rewrites of ISZERO results, side conditions by grind" }
register_option verify.eval.c.debug : Bool := {
  defValue := false
  descr := "lane C stepper: log grind failures" }
register_option verify.eval.c.stats : Bool := {
  defValue := false
  descr := "lane C stepper: report counters and timings" }

/-- A conditional rewrite: ISZERO of a word known to be zero. -/
theorem iszero_of_eq {x : EthLib.Base.U256} (h : x = 0) : (if x = 0 then (1 : EthLib.Base.U256) else 0) = 1 :=
  by simp [h]

/-- A conditional rewrite: ISZERO of a word known to be nonzero. -/
theorem iszero_of_ne {x : EthLib.Base.U256} (h : x ≠ 0) : (if x = 0 then (1 : EthLib.Base.U256) else 0) = 0 :=
  if_neg h

structure Stats where
  steps : Nat := 0
  splits : Nat := 0
  decided : Nat := 0
  leaves : Nat := 0
  infeasibleEgraph : Nat := 0
  infeasibleGrind : Nat := 0
  infeasibleOmega : Nat := 0
  premises : Nat := 0
  premGrind : Nat := 0
  premWalk : Nat := 0
  mkGoals : Nat := 0
  internalizeCalls : Nat := 0
  internalizedDecls : Nat := 0
  nsRules : Nat := 0
  nsApply : Nat := 0
  nsSimp : Nat := 0
  nsDischarge : Nat := 0
  nsInternalize : Nat := 0
  nsGrind : Nat := 0
  deriving Inhabited

structure Ctx where
  rules : Std.HashMap Nat (Array BackwardRule)
  zeroRule : BackwardRule
  takenRule : BackwardRule
  splitRule : BackwardRule
  closeRule : BackwardRule
  methods : Sym.Simp.Methods
  /-- Conditional rewrites, discharged by grind in the goal's own state (option condRewrite). -/
  condThms : Option Sym.Simp.Theorems
  fresh : Bool
  eager : Bool
  shareCache : Bool
  /-- Where the stepper is, for error reports. -/
  phase : IO.Ref String

structure St where
  stats : Stats := {}
  simpState : Sym.Simp.State := {}
  /-- Leaves the stepper could not close, with the reason. -/
  stuck : Array (MVarId × String) := #[]

abbrev M := ReaderT Ctx (StateRefT St Grind.GrindM)

@[inline] def timed (upd : Stats → Nat → Stats) (k : M α) : M α := do
  let t0 ← IO.monoNanosNow
  try k finally
    let t1 ← IO.monoNanosNow
    modify fun s => { s with stats := upd s.stats (t1 - t0) }

def bump (f : Stats → Stats) : M Unit := modify fun s => { s with stats := f s.stats }

def natLit? (e : Expr) : Option Nat :=
  match e.nat? with
  | some k => some k
  | none => e.rawNatLit?

/-- The frame of a goal `Triple (Step fork) (At code msg pc stack ..) R`. -/
structure Frame where
  n : Nat
  size : Nat
  pc : Nat
  stack : Expr
  post : Expr

def parseFrame? (ty : Expr) : Option Frame := do
  let ty := ty.consumeMData
  guard (ty.isAppOfArity ``EthLib.Execution.Evm.Logic.Triple 5)
  let P := ty.getArg! 3
  let R := ty.getArg! 4
  guard (P.isAppOfArity ``EthLib.Execution.Evm.Logic.At 10)
  let code := P.getArg! 1
  guard (code.isAppOfArity ``EthLib.Execution.Evm.Logic.NatCode.ofNat 2)
  let n ← natLit? (code.getArg! 0)
  let size ← natLit? (code.getArg! 1)
  let pc ← natLit? (P.getArg! 3)
  return { n, size, pc, stack := P.getArg! 4, post := R }

def postPc? (R : Expr) : Option Nat := do
  guard (R.isAppOfArity ``EthLib.Execution.Evm.Logic.At 10)
  natLit? (R.getArg! 3)

def opByte (f : Frame) : Nat :=
  if f.pc < f.size then (f.n >>> (8 * (f.size - 1 - f.pc))) % 256 else 0

/-- The JUMPI condition: the second word of an explicit stack. -/
def jumpiCond? (stack : Expr) : Option Expr := do
  guard (stack.isAppOfArity ``List.cons 3)
  let tl := stack.getArg! 2
  guard (tl.isAppOfArity ``List.cons 3)
  return tl.getArg! 1

/-! ## Grind state: threaded or fresh -/

/-- Internalize the goal's not yet internalized hypotheses: in threaded mode only the new ones
(the parent's are in the inherited state), in fresh mode the whole context into a new goal. -/
def internalize (g : Grind.Goal) : M Grind.Goal := do
  let fresh := (← read).fresh
  let before := g.nextDeclIdx
  (← read).phase.modify (· ++ " / internalize")
  let g ← timed (fun s t => { s with nsInternalize := s.nsInternalize + t }) do
    g.mvarId.withContext do
    if fresh then
      let g ← Grind.mkGoal g.mvarId
      g.internalizeAll
    else
      g.internalizeAll
  let n := (← g.mvarId.getDecl).lctx.numIndices
  let added := if fresh then n else n - before
  let mk := if fresh then 1 else 0
  bump fun s => { s with
    internalizeCalls := s.internalizeCalls + 1
    internalizedDecls := s.internalizedDecls + added
    mkGoals := s.mkGoals + mk }
  return g

/-- Run grind on a goal whose hypotheses are internalized; true if closed. -/
def runGrind (g : Grind.Goal) : M Bool := do
  timed (fun s t => { s with nsGrind := s.nsGrind + t }) do
    let dbg := verify.eval.c.debug.get (← getOptions)
    tryCatchRuntimeEx
      (do
        match ← g.mvarId.withContext g.grind with
        | .closed => return true
        | .failed g' =>
          if dbg then logInfo m!"evm_sym grind failed on{indentD (MessageData.ofGoal g'.mvarId)}"
          return false)
      (fun e => do
        if dbg then logInfo m!"evm_sym grind threw: {e.toMessageData}"
        return false)

/-- Close a goal by refuting its context: grind on `False` in the same context and state. -/
def refute (g : Grind.Goal) : M Bool := g.mvarId.withContext do
  let m ← g.mvarId.withContext do
    mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
  let g' ← internalize { g with mvarId := m.mvarId! }
  unless ← m.mvarId!.isAssigned do
    unless ← runGrind g' do return false
  g.mvarId.withContext do
    let ty ← g.mvarId.getType
    g.mvarId.assign (← mkFalseElim ty (← instantiateMVars m))
  return true

/-! ## Premises -/

def simpGoal (g : Grind.Goal) : M Grind.SimpGoalResult := do
  timed (fun s t => { s with nsSimp := s.nsSimp + t }) do
    let ctx ← read
    let s0 := (← get).simpState
    let st := if ctx.shareCache then s0 else {}
    g.mvarId.withContext do
    let methods ← match ctx.condThms with
      | none => pure ctx.methods
      | some thms =>
        -- the discharger runs grind on a copy of this goal's own (internalized) state: facts of
        -- sibling branches are not in it
        let dg ← if ctx.fresh then Grind.mkGoal g.mvarId >>= (·.internalizeAll) else pure g
        let d ← dg.mkSymSimpDischarger
        pure { ctx.methods with post := ctx.methods.post >> thms.rewrite d }
    let (r, st') ← Sym.Simp.SimpM.run (Sym.Simp.simp (← g.mvarId.getType)) methods {} st
    modify fun s => { s with simpState := st' }
    match ← r.toSimpGoalResult g.mvarId with
    | .noProgress => return .noProgress
    | .closed => return .closed
    | .goal m => return .goal { g with mvarId := m }

/-- A `walk n size size 0 d = true` on literals: evaluated here to select it, then proved by
`Eq.refl true`, which the kernel checks by evaluation (as `decide +kernel` does). -/
def tryWalk (g : Grind.Goal) : M Bool := do
  let ty := (← instantiateMVars (← g.mvarId.getType)).consumeMData
  let some (_, lhs, rhs) := ty.eq? | return false
  -- (the walk's arguments are literals, so no local context is needed)
  unless rhs.isConstOf ``Bool.true do return false
  unless lhs.isAppOfArity ``EthLib.Execution.Evm.Logic.NatCode.walk 5 do return false
  let args := lhs.getAppArgs
  let some n := natLit? args[0]! | return false
  let some size := natLit? args[1]! | return false
  let some fuel := natLit? args[2]! | return false
  let some pc := natLit? args[3]! | return false
  let some d := natLit? args[4]! | return false
  unless EthLib.Execution.Evm.Logic.NatCode.walk n size fuel pc d do return false
  g.mvarId.assign (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  bump fun s => { s with premWalk := s.premWalk + 1 }
  return true

/-- Prove one premise: Sym.simp, an assumption, the walk, then grind in the inherited state. -/
def discharge (g : Grind.Goal) (allowGrind := true) : M Bool := g.mvarId.withContext do
  bump fun s => { s with premises := s.premises + 1 }
  timed (fun s t => { s with nsDischarge := s.nsDischarge + t }) do
    let g ← match ← simpGoal g with
      | .closed => return true
      | .noProgress => pure g
      | .goal g' => pure g'
    if ← withReducible g.mvarId.assumptionCore then return true
    if ← tryWalk g then return true
    unless allowGrind do return false
    bump fun s => { s with premGrind := s.premGrind + 1 }
    let g' ← internalize g
    if ← g'.mvarId.isAssigned then return true
    runGrind g'

/-! ## Steps -/

def isContinuation (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  ty.isAppOf ``EthLib.Execution.Evm.Logic.Triple || ty.isForall

/-- Apply a rule; on success discharge its premises and return the continuations. -/
def applyRule (g : Grind.Goal) (rule : BackwardRule) : M (Option (List Grind.Goal)) := do
  let r ← timed (fun s t => { s with nsApply := s.nsApply + t }) (g.apply rule)
  match r with
  | .failed => return none
  | .goals gs =>
    let mut conts := #[]
    for g' in gs do
      let ty ← instantiateMVars (← g'.mvarId.getType)
      if isContinuation ty then
        conts := conts.push g'
      else unless ← discharge g' do
        throwError "evm_sym: premise not proved{indentExpr ty}"
    return some conts.toList

def stuck (g : Grind.Goal) (why : String) : M Unit := g.mvarId.withContext do
  bump fun s => { s with leaves := s.leaves + 1 }
  -- A stuck path may still be infeasible: try to refute its context.
  if ← refute g then
    bump fun s => { s with infeasibleGrind := s.infeasibleGrind + 1 }
  else
    modify fun s => { s with stuck := s.stuck.push (g.mvarId, why) }

/-- Prove `p` in `g`'s context by a quick premise (ground evaluation or an assumption). -/
def decides (g : Grind.Goal) (p : Expr) : M Bool := do
  let m ← g.mvarId.withContext do mkFreshExprSyntheticOpaqueMVar p
  discharge { g with mvarId := m.mvarId! } (allowGrind := false)

mutual
partial def run (g : Grind.Goal) : M Unit := g.mvarId.withContext do
  if ← g.mvarId.isAssigned then return
  let g ← match ← simpGoal g with
    | .closed => return
    | .noProgress => pure g
    | .goal g' => pure g'
  let ty ← instantiateMVars (← g.mvarId.getType)
  let some f := parseFrame? ty | stuck g "not a frame of a NatCode"; return
  bump fun s => { s with steps := s.steps + 1 }
  (← read).phase.set s!"pc {f.pc} opcode {opByte f}"
  if postPc? f.post == some f.pc then
    match ← applyRule g (← read).closeRule with
    | some _ => bump fun s => { s with leaves := s.leaves + 1 }
    | none => stuck g s!"at the target pc {f.pc} but the frames differ"
    return
  let b := opByte f
  if b == 0x57 then
    jumpi g f
    return
  let some rs := (← read).rules[b]? | stuck g s!"no rule for opcode {b} at pc {f.pc}"; return
  for rule in rs do
    if let some conts := ← applyRule g rule then
      if conts.isEmpty then bump fun s => { s with leaves := s.leaves + 1 }
      for c in conts do run c
      return
  stuck g s!"no rule applies for opcode {b} at pc {f.pc}"

partial def jumpi (g : Grind.Goal) (f : Frame) : M Unit := g.mvarId.withContext do
  let some c := jumpiCond? f.stack | stuck g s!"JUMPI at pc {f.pc} without two words"; return
  let ctx ← read
  let zero ← g.mvarId.withContext do
    let u ← inferType c
    let z ← mkNumeral u 0
    mkEq c z
  if ← decides g zero then
    bump fun s => { s with decided := s.decided + 1 }
    let some conts := ← applyRule g ctx.zeroRule | stuck g "jumpi_zero failed"; return
    for c in conts do run c
    return
  if ← decides g (mkNot zero) then
    bump fun s => { s with decided := s.decided + 1 }
    let some conts := ← applyRule g ctx.takenRule | stuck g "jumpi_taken failed"; return
    for c in conts do run c
    return
  bump fun s => { s with splits := s.splits + 1 }
  let some conts := ← applyRule g ctx.splitRule | stuck g "jumpi_split failed"; return
  for c in conts do
    -- each child introduces its own path condition and internalizes it into its own state
    let .goal _ c' ← Grind.Goal.intros c #[`hpath] | stuck c "intro failed"; return
    let c' ← internalize c'
    if ← c'.mvarId.isAssigned then
      bump fun s => { s with infeasibleEgraph := s.infeasibleEgraph + 1 }
      continue
    if ctx.eager then
      if ← refute c' then
        bump fun s => { s with infeasibleGrind := s.infeasibleGrind + 1 }
        continue
    run c'
end

def ruleNames : List (Nat × List Name) :=
  [(0x00, [``Verify.Eval.C.step_stop_done]),
   (0x01, [``Verify.Eval.C.step_add]), (0x03, [``Verify.Eval.C.step_sub]),
   (0x10, [``Verify.Eval.C.step_lt]), (0x11, [``Verify.Eval.C.step_gt]),
   (0x14, [``Verify.Eval.C.step_eq]), (0x15, [``Verify.Eval.C.step_iszero]),
   (0x16, [``Verify.Eval.C.step_and]), (0x17, [``Verify.Eval.C.step_or]),
   (0x18, [``Verify.Eval.C.step_xor]), (0x19, [``Verify.Eval.C.step_not]),
   (0x1b, [``Verify.Eval.C.step_shl]), (0x1c, [``Verify.Eval.C.step_shr]),
   (0x34, [``Verify.Eval.C.step_callvalue]), (0x35, [``Verify.Eval.C.step_calldataload]),
   (0x36, [``Verify.Eval.C.step_calldatasize]), (0x50, [``Verify.Eval.C.step_pop]),
   (0x56, [``Verify.Eval.C.step_jump]), (0x5b, [``Verify.Eval.C.step_jumpdest]),
   (0x5f, [``Verify.Eval.C.step_push0]),
   (0xfd, [``Verify.Eval.C.step_revert_reverted, ``Verify.Eval.C.step_revert_done])] ++
  (List.range 32).map (fun i => (0x60 + i, [Name.mkStr `Verify.Eval.C s!"step_push{i+1}"])) ++
  (List.range 8).map (fun i => (0x80 + i, [Name.mkStr `Verify.Eval.C s!"step_dup{i+1}"])) ++
  (List.range 8).map (fun i => (0x90 + i, [Name.mkStr `Verify.Eval.C s!"step_swap{i+1}"]))

def simpRewrites : List Name :=
  [``Nat.sub_sub, ``List.length_cons, ``List.length_nil, ``eq_self]

/-- Extra rewrite rules for the frame (`evm_sym ... using [..]`): local hypotheses such as
`msg.data = cdOf ..`, or global lemmas; their side conditions are discharged by `Sym.simp` itself. -/
def mkExtra (extra : Array Syntax) : MetaM Sym.Simp.Theorems := do
  let mut thms : Sym.Simp.Theorems := {}
  for id in extra do
    if let some decl := (← getLCtx).findFromUserName? id.getId then
      thms := thms.insert (← Sym.Simp.mkTheoremFromExpr decl.toExpr)
    else
      let n ← realizeGlobalConstNoOverload id
      for t in ← Sym.Simp.mkTheoremsFromDecl n do thms := thms.insert t
  return thms

def mkCtx (opts : Options) (extra : Sym.Simp.Theorems := {}) (hasExtra := false) : MetaM Ctx := do
  let mut rules : Std.HashMap Nat (Array BackwardRule) := {}
  for (b, ns) in ruleNames do
    rules := rules.insert b (← ns.toArray.mapM fun n => mkBackwardRuleFromDecl n)
  let mut thms : Sym.Simp.Theorems := {}
  for n in simpRewrites do
    thms := thms.insert (← Sym.Simp.mkTheoremFromDecl n)
  let post := Sym.Simp.evalGround {} >> thms.rewrite
  let post := if hasExtra then post >> extra.rewrite Sym.Simp.dischargeSimpSelf else post
  let methods : Sym.Simp.Methods := { pre := Sym.Simp.simpControl, post }
  return {
    rules
    zeroRule := ← mkBackwardRuleFromDecl ``Verify.Eval.C.step_jumpi_zero
    takenRule := ← mkBackwardRuleFromDecl ``Verify.Eval.C.step_jumpi_taken
    splitRule := ← mkBackwardRuleFromDecl ``Verify.Eval.C.step_jumpi_split
    closeRule := ← mkBackwardRuleFromDecl ``Verify.Eval.C.at_close
    methods
    condThms := ← if verify.eval.c.condRewrite.get opts then
        some <$> [``iszero_of_eq, ``iszero_of_ne].foldlM
          (fun (t : Sym.Simp.Theorems) n => return t.insert (← Sym.Simp.mkTheoremFromDecl n)) {}
      else pure none
    fresh := verify.eval.c.fresh.get opts
    eager := verify.eval.c.eager.get opts
    shareCache := verify.eval.c.shareCache.get opts
    phase := ← IO.mkRef "start" }

def Stats.render (s : Stats) : String :=
  let ms (ns : Nat) := s!"{ns / 1000000}.{(ns % 1000000) / 100000}"
  s!"evm_sym stats: steps={s.steps} splits={s.splits} decided={s.decided} leaves={s.leaves} " ++
  s!"infeasible(egraph/grind/omega)={s.infeasibleEgraph}/{s.infeasibleGrind}/{s.infeasibleOmega} " ++
  s!"premises={s.premises} premGrind={s.premGrind} premWalk={s.premWalk} mkGoals={s.mkGoals} " ++
  s!"internalizeCalls={s.internalizeCalls} internalizedDecls={s.internalizedDecls} " ++
  s!"ms(rules/apply/simp/discharge/internalize/grind)={ms s.nsRules}/{ms s.nsApply}/{ms s.nsSimp}/" ++
  s!"{ms s.nsDischarge}/{ms s.nsInternalize}/{ms s.nsGrind}"

/-- Run the stepper on one goal; returns the leaves it could not close and its counters. -/
def stepGoal (mvarId : MVarId) (extra : Array Syntax := #[]) :
    MetaM (Array (MVarId × String) × Stats) := do
  let opts ← getOptions
  let t0 ← IO.monoNanosNow
  let ex ← mvarId.withContext (mkExtra extra)
  let ctx ← mkCtx opts ex (!extra.isEmpty)
  let t1 ← IO.monoNanosNow
  let params ← Grind.mkDefaultParams {}
  Grind.GrindM.run (params := params) do
    let root ← mvarId.withContext (Grind.mkGoal mvarId)
    let stRef ← IO.mkRef ({ stats := { nsRules := t1 - t0 } } : St)
    let body : Grind.GrindM Unit := do
      let ((), st) ← (do
          let root ← internalize root
          run root : M Unit).run ctx |>.run (← stRef.get)
      stRef.set st
    tryCatchRuntimeEx body fun e => do
      throwError m!"evm_sym: exception at {← ctx.phase.get}: {e.toMessageData}"
    let st ← stRef.get
    return (st.stuck, st.stats)

syntax (name := evmSym) "evm_sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (" using " "[" ident,* "]")? : tactic

/-- `evm_sym [ls]`: rewrite the goal with `ls` (the code's equations, so the code is a literal
`NatCode.ofNat n size`), unfold `Spec`, introduce the binders, then run the stepper. Leaves the
stepper cannot close are retried with `exfalso; bv_omega`, and otherwise reported as errors. -/
@[tactic evmSym] def evalEvmSym : Tactic := fun stx => do
  match stx with
  | `(tactic| evm_sym $[[$ls,*]]? $[using [$us,*]]?) =>
    let ls := ls.map (·.getElems) |>.getD #[]
    let us : Array Syntax := (us.map (·.getElems.map (·.raw))).getD #[]
    unless ls.isEmpty do
      evalTactic (← `(tactic| simp only [$ls,*]))
    evalTactic (← `(tactic| ((try unfold EthLib.Execution.Evm.Logic.Spec); intros)))
    let g ← getMainGoal
    let (stuck, stats) ← stepGoal g us
    let mut stats := stats
    let mut left := #[]
    for (m, why) in stuck do
      let s ← saveState
      let ok ← tryCatchRuntimeEx
        (do
          setGoals [m]
          evalTactic (← `(tactic| (exfalso; symex_omega)))
          pure true)
        (fun _ => do s.restore; pure false)
      if ok then
        stats := { stats with infeasibleOmega := stats.infeasibleOmega + 1 }
      else
        left := left.push (m, why)
    if verify.eval.c.stats.get (← getOptions) then
      logInfo stats.render
    unless left.isEmpty do
      let msgs := left.map fun (_, why) => why
      let goals : MessageData := if verify.eval.c.debug.get (← getOptions) then
          MessageData.joinSep (left.toList.map fun (m, _) => MessageData.ofGoal m) "\n" else ""
      throwError m!"evm_sym: {left.size} open path(s): {msgs.toList}{goals}"
    setGoals []
  | _ => throwUnsupportedSyntax

end Verify.Eval.C.Stepper
