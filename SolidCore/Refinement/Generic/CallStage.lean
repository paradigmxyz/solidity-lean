import SolidCore.Refinement.Generic.CallSourceRun
import SolidCore.Refinement.Generic.CallMirRun
import SolidCore.Refinement.Solar.AssembleCallOpen

/-!
# The generic source stage with one external call, in every open world

`checkC` is the kernel's check of a contract's functions against solar's first lowered MIR: for each
function, SolidCore's call tree (`eraseFnC`) and the MIR's (`symTreeC`) agree (`CTree.agree`), and a
function that calls out calls argument `j` (the function's declared target). `stageC`: in every open
world whose answers to static calls to code fit (`AssembleCallOpen.Fits`) and every MIR oracle that
agrees with it (`CallsAgree`), SolidCore refines the MIR on every valid call (`CValid`): a call of a
checked function on argument words below `2 ^ 256`, with no value, from any storage, whose target
argument is neither the contract itself nor, in its low 160 bits, an address of EthLib's Fusaka
precompile set. `totalC`: SolidCore runs every valid call
to an end in such a world.
-/

namespace SolidCore.Refinement.Generic
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.CallNode EvmCompiler.Simulation

/-! ## Argument checks of call trees -/

theorem paramGuardsC_eval (ρ : Val) (A : Callee) (T : CTree) (hρ : ∀ a ∈ ρ.args, a < wordSize) :
    ∀ (ws : List Nat) (i : Nat),
      (paramGuardsC ws i T).eval ρ A =
        if argsClean ws (ρ.args.drop i) then T.eval ρ A
        else { success := false, output := [], logs := [], store := ρ.store }
  | [], i => by simp [paramGuardsC, argsClean]
  | w :: ws, i => by
    rw [argsClean_drop ρ hρ, paramGuardsC]
    have ih := paramGuardsC_eval ρ A T hρ ws (i + 1)
    split
    · rename_i hw
      simp only [CTree.eval, eval_gt_bound ρ _ (show w < wordSize by omega), ih,
        argOk_lt _ (show w < wordSize by omega)]
      by_cases h : (WExpr.arg i).eval ρ ≤ w <;> simp [h, Tree.eval]
    · rename_i hw
      split
      · rename_i hb
        simp only [CTree.eval, ih, argOk_eq, show ¬ w < wordSize by omega, ↓reduceIte, hb, and_self]
        by_cases h : sextNat (w - wordSize) ((WExpr.arg i).eval ρ) = (WExpr.arg i).eval ρ
        · simp [h, (eval_sextGuard ρ hb (.arg i)).mpr h]
        · have h0 : ¬ (sextGuard (w - wordSize) (.arg i)).eval ρ = 0 :=
            fun h' => h ((eval_sextGuard ρ hb _).mp h')
          simp [h, h0, Tree.eval]
      · rename_i hb
        have hok : argOk w ((WExpr.arg i).eval ρ) = true := by
          have := WExpr.eval_lt ρ (.arg i)
          rw [argOk_eq]
          split
          · simp; omega
          · simp [hb]
        simp [ih, hok]

theorem paramGuardsC_reach (ρ : Val) (T : CTree) (hρ : ∀ a ∈ ρ.args, a < wordSize) :
    ∀ (ws : List Nat) (i : Nat),
      (paramGuardsC ws i T).reach ρ = if argsClean ws (ρ.args.drop i) then T.reach ρ else none
  | [], i => by simp [paramGuardsC, argsClean]
  | w :: ws, i => by
    rw [argsClean_drop ρ hρ, paramGuardsC]
    have ih := paramGuardsC_reach ρ T hρ ws (i + 1)
    split
    · rename_i hw
      simp only [CTree.reach, eval_gt_bound ρ _ (show w < wordSize by omega), ih,
        argOk_lt _ (show w < wordSize by omega)]
      by_cases h : (WExpr.arg i).eval ρ ≤ w <;> simp [h]
    · rename_i hw
      split
      · rename_i hb
        simp only [CTree.reach, ih, argOk_eq, show ¬ w < wordSize by omega, ↓reduceIte, hb, and_self]
        by_cases h : sextNat (w - wordSize) ((WExpr.arg i).eval ρ) = (WExpr.arg i).eval ρ
        · simp [h, (eval_sextGuard ρ hb (.arg i)).mpr h]
        · have h0 : ¬ (sextGuard (w - wordSize) (.arg i)).eval ρ = 0 :=
            fun h' => h ((eval_sextGuard ρ hb _).mp h')
          simp [h, h0]
      · rename_i hb
        have hok : argOk w ((WExpr.arg i).eval ρ) = true := by
          have := WExpr.eval_lt ρ (.arg i)
          rw [argOk_eq]
          split
          · simp; omega
          · simp [hb]
        simp [ih, hok]

/-! ## The check -/

/-- A function of the call route: its selector, its number of argument words, and the argument
whose word its external call calls, if it makes one. -/
structure CFn where
  sel : Nat
  n : Nat
  target : Option Nat
  deriving DecidableEq, Repr

/-- Every external call of a call tree calls argument `j`. -/
def CTree.targetsArg (j : Nat) : CTree → Bool
  | .tree _ => true
  | .ite _ a b => a.targetsArg j && b.targetsArg j
  | .call r _ _ _ => r.target == .arg j

/-- A call tree with no external call. -/
def CTree.callFree : CTree → Bool
  | .tree _ => true
  | .ite _ a b => a.callFree && b.callFree
  | .call _ _ _ _ => false

/-- Whether the function `f` lowers to `m`: SolidCore dispatches its selector to a function with `f`'s
parameter count, whose call tree agrees with the symbolic run of `m` on the selector; a function
with a target makes its calls to that argument, one without makes none. -/
def checkCFn (fuel mirFuel : Nat) (core : Contract) (m : Module) (env : EnvFlags) (f : CFn) : Bool :=
  decide (f.sel < 2 ^ 32) &&
    match core.findFunctionBySelector? f.sel with
    | none => false
    | some fn =>
      decide (fn.params.length = f.n) &&
        match eraseFnC (envOf core) fuel fn, symTreeC m f.sel f.n mirFuel env with
        | some t1, some t2 =>
          CTree.agree t1 t2 &&
            match f.target with
            | some j => decide (j < f.n) && t1.targetsArg j
            | none => t1.callFree
        | _, _ => false

/-- Whether every function of `fns` lowers to `m`. -/
def checkC (fuel mirFuel : Nat) (core : Contract) (m : Module) (fns : List CFn) (env : EnvFlags := .off) :
    Bool :=
  fns.all (checkCFn fuel mirFuel core m env)

/-- An address outside EthLib's Fusaka precompile set (`0x01`–`0x11` and `0x100`) is outside
SolidCore's (`0x01`–`0x0a`). -/
theorem kind_none_of_fusaka {w : Nat} (hw : w < 2 ^ 160)
    (h : EthLib.Execution.Evm.Precompiles.isPrecompile .fusaka w = false) :
    SolidCore.Solidity.Shared.Precompile.kindOfAddress? w = none := by
  open SolidCore.Solidity.Shared in
  unfold Precompile.kindOfAddress?
  rw [List.find?_eq_none]
  intro k hk hk'
  have hlt : w < SolidCore.Solidity.Shared.wordModulus := lt_trans hw (by decide)
  simp only [SolidCore.Solidity.Shared.Precompile.mainnetKinds, List.mem_cons, List.not_mem_nil,
    or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [SolidCore.Solidity.Shared.Precompile.address, SolidCore.Solidity.Shared.Call.wordEq,
      SolidCore.Solidity.Shared.Account.wordEq, SolidCore.Solidity.Shared.norm,
      Nat.mod_eq_of_lt hlt, beq_iff_eq] at hk'
    rw [Nat.mod_eq_of_lt (by decide : (_ : Nat) < SolidCore.Solidity.Shared.wordModulus)] at hk'
    subst hk'
    revert h; decide

/-- **The valid calls**: a call of a function of `fns` on argument words below `2 ^ 256`, with no
value, from any storage, whose target argument, for a function that calls out, is not the contract
itself and whose low 160 bits are no address of EthLib's Fusaka precompile set
(`EthLib.Execution.Evm.Precompiles.isPrecompile .fusaka`: `0x01`–`0x11` and `0x100`, which
contains SolidCore's `0x01`–`0x0a`: `kind_none_of_fusaka`). Nothing is said of the code at the
target: it may be empty or a delegation. -/
def CValid (fns : List CFn) (call : Call) : Prop :=
  ∃ f ∈ fns, ∃ args σ, args.length = f.n ∧ (∀ a ∈ args, a < 2 ^ 256) ∧
    call = { calldata := Abi.calldata f.sel args, callvalue := 0, storage := σ } ∧
    ∀ j, f.target = some j → args.getD j 0 ≠ selfAddress ∧
      EthLib.Execution.Evm.Precompiles.isPrecompile .fusaka (args.getD j 0 % 2 ^ 160) = false


/-! ## Pieces of the stage -/

theorem eraseFnC_cases {E : EraseEnv} {fuel : Nat} {fn : FunctionDef} {T : CTree}
    (h : eraseFnC E fuel fn = some T) :
    (∃ t, eraseFn E fuel fn = some t ∧ T = .tree t) ∨
      ∃ ws r k t, widthsOf fn.params fn.paramAbiCleanups = some ws ∧ fn.returns.all wordBinding = true ∧
        eraseStmtC { E with facts := argFacts ws 0 } fn.params.length fuel fn.body (initState fn) = some (r, k) ∧
        brTree fn (argFacts ws 0) k = some t ∧ T = paramGuardsC ws 0 (.call r [] fn.params.length t) := by
  unfold eraseFnC at h
  split at h
  · rename_i t ht
    simp only [Option.some.injEq] at h
    exact Or.inl ⟨t, ht, h.symm⟩
  · split at h
    · simp at h
    · rename_i ws hw
      split at h
      · rename_i hret
        split at h
        · rename_i r k hrk
          split at h
          · rename_i t ht
            simp only [Option.some.injEq] at h
            exact Or.inr ⟨ws, r, k, t, hw, hret, hrk, ht, h.symm⟩
          · simp at h
        · simp at h
      · simp at h

theorem targetsArg_paramGuardsC (j : Nat) (T : CTree) : ∀ (ws : List Nat) (i : Nat),
    (paramGuardsC ws i T).targetsArg j = T.targetsArg j
  | [], _ => rfl
  | w :: ws, i => by
    simp only [paramGuardsC]
    split <;> (try split) <;> simp [CTree.targetsArg, targetsArg_paramGuardsC j T ws (i + 1)]

theorem callFree_paramGuardsC (T : CTree) : ∀ (ws : List Nat) (i : Nat),
    (paramGuardsC ws i T).callFree = T.callFree
  | [], _ => rfl
  | w :: ws, i => by
    simp only [paramGuardsC]
    split <;> (try split) <;> simp [CTree.callFree, callFree_paramGuardsC T ws (i + 1)]

theorem CallFacts.extend {sel n : Nat} {args : List Nat} {st : Nat → Nat} {c : Nat} {call : Call}
    (hn : args.length = n) (h : CallFacts sel n ⟨args, st, solHash, c⟩ call) (extra : List Nat) :
    CallFacts sel n ⟨args ++ extra, st, solHash, c⟩ call where
  value := h.value
  size := h.size
  args i hi hw := by rw [h.args i hi hw, arg_append _ _ _ _ _ (by omega)]
  selector := h.selector
  store := h.store
  ok := h.ok

theorem callFlag_toNat (o : Oracle) (w : List SolarTV.Machine.Event) :
    (callFlag o w).toNat = if callFlag o w = 1 then 1 else 0 := by
  unfold callFlag
  split <;> simp

/-- **The oracle's answer to the external call, from `CallsAgree`**: the world's answer to the
request the source sent, in the MIR world that ends with the same call. -/
theorem ansAt_of_agree {o : Oracle} {W : World} (hagree : CallsAgree o W) {n : Nat} {ρ : Val}
    {world : SolidCore.Solidity.Shared.OpenWorld} {request : CallRequest} {resp : CallResponse}
    (hans : W.ans [] (.external world (.call request)) = some resp) {r : CReq}
    (hreq : ReqOK ρ r request) (hsize : resp.returnData.size < 2 ^ 256)
    (hval : ρ.withAns n (toCAns resp) = ρ)
    (hstore : ∀ slot < 2 ^ 256, storageIn world slot = ρ.store slot)
    (htr : ∀ slot < 2 ^ 256, transientIn world slot = 0)
    (hcodes : ∀ x < 2 ^ 160, (codeIn world x).isEmpty =
      (SolidCore.Solidity.Shared.Account.codeAt (W.codes.getD []) x).isEmpty)
    {pre : List SolarTV.Machine.Event} {seen : List (BitVec 256)} {input : List Memory.Byte}
    {sto : BitVec 256 → BitVec 256}
    (hpre : machineCalls pre = []) (htgt : (seen.getD 1 0).toNat = r.target.eval ρ)
    (hin : input.map BitVec.toNat = r.input.map (OByte.eval ρ))
    (hsto : ∀ k : BitVec 256, (sto k).toNat = ρ.store k.toNat) :
    AnsAt o n ρ (pre ++ [SolarTV.Machine.Event.call .staticcall seen input sto (fun _ => 0)]) (toCAns resp) := by
  have hlen : (toCAns resp).data.length = resp.returnData.size := by simp [toCAns, byteArrayToBytes_eq]
  have hcalls : machineCalls (pre ++ [SolarTV.Machine.Event.call .staticcall seen input sto (fun _ => 0)]) =
      sourceCalls ([] ++ [⟨.external world (.call request), resp⟩]) := by
    rw [machineCalls_append, hpre]
    simp only [machineCalls, sourceCalls, List.nil_append, hreq.kind, machineKind, hreq.callee,
      hreq.value, hreq.input, htgt, hin]
    simp
  have hcodes' : CodesAgree o (pre ++ [SolarTV.Machine.Event.call .staticcall seen input sto (fun _ => 0)]).dropLast (codeIn world) := by
    rw [List.dropLast_concat]
    intro x hx
    rw [hagree.codes pre hpre x hx, hcodes x hx]
  obtain ⟨hflag, -, hrest⟩ := hagree.calls [] world request resp hans
    (pre ++ [SolarTV.Machine.Event.call .staticcall seen input sto (fun _ => 0)]) .staticcall seen input sto (fun _ => 0)
    (by simp) hcalls
    (fun slot hs => ⟨by rw [hsto, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs, hstore slot hs],
      by rw [htr slot hs]; rfl⟩) hcodes'
  refine ⟨hval, by rw [hlen]; exact hsize, ?_, ?_, ?_⟩
  · rw [callFlag_toNat]
    have hok : (toCAns resp).ok = resp.success := rfl
    rw [hok]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hflag.mp h1) h2
    · exact absurd (hflag.mpr h2) h1
    · rfl
  · intro rest hr
    rw [(hrest rest hr).1, hlen, Nat.mod_eq_of_lt hsize]
  · intro rest hr j hj
    rw [hlen] at hj
    rw [(hrest rest hr).2.1 j hj (lt_trans hj hsize)]
    simp [toCAns, byteArrayToBytes_eq, List.getD_eq_getElem?_getD, hj]


/-! ## The stage -/

/-- The answers to static calls to code of a world that fits are shorter than `2 ^ 256` bytes. -/
theorem fits_static {W : World} (hfits : Solar.AssembleCallOpen.Fits W) :
    ∀ world request a, W.ans [] (.external world (.call request)) = some a →
      request.kind = .staticcall →
      SolidCore.Solidity.Shared.Precompile.kindOfAddress? (addressToWord request.codeAddress) = none →
      a.returnData.size < 2 ^ 256 := by
  intro world request a hans hk hpre
  apply hfits.2 [] world request a hans
  simp [Witness.toCode, Witness.prePath, Witness.isStaticM, hk, machineKind, hpre]

/-- **The generic source stage with one external call, in every open world that fits**: a checked
contract whose constructor leaves no storage, logs, transient storage, adopted world or seeded
accounts, and a lowered MIR module that `checkC` accepts, give the stage from SolidCore in `W` to the
module's lowered MIR under every oracle that agrees with `W`, on every valid call. -/
theorem stageC (W : World) (o : Oracle) (hagree : CallsAgree o W) (hW : W.Open)
    (hfits : Solar.AssembleCallOpen.Fits W) {fuel mirFuel : Nat}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {d : SolidCore.Solidity.Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d [])
    (hcc : c.core.context.accountCodes = []) (hcb : c.core.context.accountBalances = [])
    (hch : c.core.context.accountCodehashes = []) (hdt : d.transient.toList = []) (hde : d.envWorld? = none)
    {m : Module} {fns : List CFn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : checkC fuel mirFuel c.core m fns env = true) :
    Stage (solidCoreIn W fuel) (mirSem o) c m (CValid fns) := by
  rintro _ ⟨f, hf, args, σ, hlen, hargs, rfl, htv⟩ obs hrun
  have hcf := List.all_eq_true.mp hchk f hf
  unfold checkCFn at hcf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hcf⟩ := hcf
  cases hfind : c.core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  simp only [hfind, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hpl, hcf⟩ := hcf
  cases hT1 : eraseFnC (envOf c.core) fuel fn with
  | none => simp [hT1] at hcf
  | some T1 =>
  cases hT2 : symTreeC m f.sel f.n mirFuel env with
  | none => simp [hT1, hT2] at hcf
  | some T2 =>
  simp only [hT1, hT2, Bool.and_eq_true] at hcf
  obtain ⟨hag, htg⟩ := hcf
  change Source.runIn W fuel c _ = some obs at hrun
  have hargsW : ∀ a ∈ args, a < wordSize := hargs
  have hlen' : args.length = fn.params.length := by rw [hlen, hpl]
  have hcf0 := callFacts f.sel hsel args hargs σ
  rw [hlen] at hcf0
  show (moduleSem o).run m _ = some obs
  rcases eraseFnC_cases hT1 with ⟨t, ht, rfl⟩ | ⟨ws, r, k, t, hw, hret, hrk, ht, rfl⟩
  · -- a function with no external call
    rw [source_runIn W hd (fun _ h => absurd h List.not_mem_nil) hsel hfind ht args hlen' hargs] at hrun
    cases hrun
    have hO : OAns o (fun _ _ => ⟨false, []⟩) ⟨args, slotValue σ, solHash, callerWord⟩ f.n T2 := by
      intro r2 ws2 n' hr
      obtain ⟨r1, ws1, h1, -, -⟩ := (CTree.agree_sound hag _ (fun _ _ => ⟨false, []⟩)).2.2 r2 ws2 n' hr
      simp [CTree.reach] at h1
    rw [symTreeC_sound hcf0 o m (henv.envAsk args _) hT2 _ hO,
      ← (CTree.agree_sound hag _ (fun _ _ => ⟨false, []⟩)).1]
    rfl
  · -- a function of the call fragment
    have hnf : (paramGuardsC ws 0 (.call r [] fn.params.length t)).callFree = false := by
      rw [callFree_paramGuardsC]; rfl
    cases htarget : f.target with
    | none => simp [htarget, hnf] at htg
    | some j =>
    simp only [htarget, Bool.and_eq_true, decide_eq_true_eq] at htg
    obtain ⟨hj, htgt⟩ := htg
    rw [targetsArg_paramGuardsC] at htgt
    simp only [CTree.targetsArg, beq_iff_eq] at htgt
    obtain ⟨hnself, hnfus⟩ := htv j htarget
    have hnpre := kind_none_of_fusaka (Nat.mod_lt _ (by decide)) hnfus
    by_cases hclean : argsClean ws args = true
    · obtain ⟨world, request, resp, hresp, hreq, hst, htr, hcodes, hsize, hrunC⟩ :=
        source_runC W hW (fun h world request a hans hk slot => (hagree.static h world request a hans hk slot).1)
          (fits_static hfits) hfits.1 hd hcc hcb hch hdt hde hsel hfind hw hret hrk ht (by omega) htgt args
          hlen' hargs hclean hnself hnpre σ
      rw [hrunC] at hrun
      cases hrun
      have hwsl : ws.length = args.length := by rw [hlen']; exact widthsOf_length hw
      have hρargs : ∀ a ∈ (callVal args σ (toCAns resp)).args, a < wordSize := by
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact hargs a h
        · exact ansWords_lt _ a h
      have hcl : argsClean ws ((callVal args σ (toCAns resp)).args.drop 0) = true := by
        simp only [callVal, List.drop_zero, argsClean_append ws args _ hwsl]; exact hclean
      have hval : (callVal args σ (toCAns resp)).withAns f.n (toCAns resp) =
          callVal args σ (toCAns resp) := by
        unfold callVal; rw [← hlen]; exact withAns_append args _ _ _ _
      have hO : OAns o (fun _ _ => toCAns resp) (callVal args σ (toCAns resp)) f.n T2 := by
        intro r2 ws2 n' hr pre seen input sto hpre htgt2 hin hsto
        obtain ⟨r1, ws1, h1, hre, hwe⟩ :=
          (CTree.agree_sound hag _ (fun _ _ => toCAns resp)).2.2 r2 ws2 n' hr
        rw [paramGuardsC_reach _ _ hρargs, if_pos hcl] at h1
        simp only [CTree.reach, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨hr1, hws1, -⟩ := h1
        subst hr1 hws1
        have ht2 : (seen.getD 1 0).toNat = r.target.eval (callVal args σ (toCAns resp)) := by
          rw [htgt2]; exact congrArg CReqV.target hre
        have hi2 : input.map BitVec.toNat = r.input.map (OByte.eval (callVal args σ (toCAns resp))) := by
          rw [hin]; exact congrArg CReqV.input hre
        have hs2 : ∀ kk : BitVec 256, (sto kk).toNat = (callVal args σ (toCAns resp)).store kk.toNat := by
          intro kk; rw [hsto, hwe]; rfl
        exact ansAt_of_agree hagree hresp hreq hsize hval
          (fun slot hs => by rw [hst slot hs, Nat.mod_eq_of_lt (slotValue_lt σ slot)]; rfl)
          htr hcodes hpre ht2 hi2 hs2
      rw [symTreeC_sound (CallFacts.extend hlen hcf0 _) o m (henv.envAsk _ _) hT2 _ hO,
        ← (CTree.agree_sound hag _ (fun _ _ => toCAns resp)).1]
      have he := paramGuardsC_eval (callVal args σ (toCAns resp)) (fun _ _ => toCAns resp)
        (.call r [] fn.params.length t) hρargs ws 0
      rw [if_pos hcl] at he
      exact congrArg (fun R => some (Res.obs R)) he
    · have hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .error .empty := by
        have := decode_args hw args hlen' hargs
        rw [if_neg hclean] at this
        exact this
      rw [runIn_rejected W hd hsel hfind args hargs hdec σ] at hrun
      cases hrun
      have hcl : argsClean ws ((⟨args, slotValue σ, solHash, callerWord⟩ : Val).args.drop 0) = false := by
        simpa using hclean
      have hO : OAns o (fun _ _ => ⟨false, []⟩) ⟨args, slotValue σ, solHash, callerWord⟩ f.n T2 := by
        intro r2 ws2 n' hr
        obtain ⟨r1, ws1, h1, -, -⟩ := (CTree.agree_sound hag _ (fun _ _ => ⟨false, []⟩)).2.2 r2 ws2 n' hr
        rw [paramGuardsC_reach _ _ hargsW, hcl] at h1
        simp at h1
      rw [symTreeC_sound hcf0 o m (henv.envAsk args _) hT2 _ hO,
        ← (CTree.agree_sound hag _ (fun _ _ => ⟨false, []⟩)).1, paramGuardsC_eval _ _ _ hargsW, hcl]
      rfl

end SolidCore.Refinement.Generic

