import Contracts.CallFamilies.SkimAgree
import Contracts.CallFamilies.SyncSource
import SolidCore.Refinement.KernelRfl

namespace SolidCore.Refinement.CallFamilies

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.CallNode
open SolidCore.Solidity.Source EvmCompiler.Simulation

/-- The selector expression of pay's transfer: bytes4(keccak256("transfer(address,uint256)")). -/
def transferSelE : Expr :=
  Expr.castOp (CastKind.fixedBytes 32) 4 (Expr.keccak256 (Expr.byteArray
    [116, 114, 97, 110, 115, 102, 101, 114, 40, 97, 100, 100, 114, 101, 115, 115, 44, 117,
     105, 110, 116, 50, 53, 54, 41]))

theorem mat_bytes (ctx : Context) (rt : Runtime) (bs : List Byte) :
    rt.materializeForValueUse ctx (.bytes bs) = .ok (.bytes bs) := by
  unfold Runtime.materializeForValueUse
  rw [Runtime.materializeForValueUseFuel]
  all_goals intros
  all_goals contradiction

/-- The cast of the signature's Keccak-256 to its first four bytes. -/
def selCast : Except SolidCore.Solidity.Source.RevertData Value :=
  fixedBytesCast? 4 32 (keccakWord ([116, 114, 97, 110, 115, 102, 101, 114, 40, 97, 100, 100, 114, 101,
    115, 115, 44, 117, 105, 110, 116, 50, 53, 54, 41].map normByte))

kernel_rfl selCast_eq selCast (Except.ok (Value.fixedBytes 4
  2835717307))

/-- The selector cast as the interpreter computes it. -/
def selCast2 : Except SolidCore.Solidity.Source.RevertData Value :=
  fixedBytesCast? 4 32 (SolidCore.Solidity.Shared.norm (keccakWord (List.map normByte (List.map normByte
    [116, 114, 97, 110, 115, 102, 101, 114, 40, 97, 100, 100, 114, 101,
    115, 115, 44, 117, 105, 110, 116, 50, 53, 54, 41]))))

kernel_rfl selCast2_eq selCast2 (Except.ok (Value.fixedBytes 4 2835717307))

/-- The selector of transfer, as SolidCore holds a bytes4 (right-aligned). -/
abbrev transferWord : Nat := 2835717307

theorem dbind {ε α β : Type} (a : α) (f : α → Interaction ε β) :
    (Interaction.done (Except.ok a)).bind f = f a := rfl

theorem sel_eval (ctx : Context) (rt : Runtime) :
    transferSelE.evalWithRuntimeByContext ctx rt = .ok (.fixedBytes 4 transferWord, rt) := by
  simp only [transferSelE, Expr.evalWithRuntimeByContext, Expr.eval, Expr.orderFuel, Expr.evalFuel]
  simp only [bind, pure, liftM, monadLift, MonadLift.monadLift, SolI.ofExcept, ipure_bind, mat_bytes]
  have h := selCast_eq
  unfold selCast at h
  simp only [List.map_cons, List.map_nil] at h
  rw [dbind]
  simp only [Value.asBytes?, ipure_bind, Value.expectWord]
  rw [dbind]
  have h2 := selCast2_eq
  unfold selCast2 at h2
  rw [h2]
  rfl

theorem selF (n : Nat) (ctx : Context) (rt : Runtime) :
    Expr.evalFuel (n + 4) ctx rt transferSelE = pure (.fixedBytes 4 transferWord, rt) := by
  simp only [transferSelE, Expr.evalFuel]
  simp only [bind, pure, liftM, monadLift, MonadLift.monadLift, SolI.ofExcept, ipure_bind, mat_bytes]
  rw [dbind]
  simp only [Value.asBytes?, ipure_bind, Value.expectWord]
  rw [dbind]
  have h2 := selCast2_eq
  unfold selCast2 at h2
  rw [h2]
  rfl

theorem varF (n : Nat) (ctx : Context) (rt : Runtime) (x : String) (w : Nat)
    (hb : rt.lookupStorageBase? x = none) (hl : rt.lookupLocal? x = some (.word w)) :
    Expr.evalFuel (n + 1) ctx rt (Expr.var x) = pure (.word w, rt) := by
  simp only [Expr.evalFuel, hb, hl]
  rfl

def selBytes : List Nat := wordToBytesBE selectorBytes (SolidCore.Solidity.Shared.norm transferWord)

kernel_rfl selBytes_eq selBytes [169, 5, 156, 187]

theorem selBytes_eq' : wordToBytesBE selectorBytes (SolidCore.Solidity.Shared.norm transferWord) =
    [169, 5, 156, 187] := selBytes_eq

/-- The input pay sends: transfer(to, amount). -/
def payInput (dst amt : Nat) : List Nat :=
  [169, 5, 156, 187] ++ wordToBytesBE Solidity.Source.wordBytes dst ++ wordToBytesBE Solidity.Source.wordBytes amt

theorem enc2 (dst amt : Nat) (hd : dst < 2 ^ 160) (ha : amt < 2 ^ 256) :
    abiEncodeValues? [Ty.address, Ty.uint256] [.word dst, .word amt] =
      some (wordToBytesBE Solidity.Source.wordBytes dst ++ wordToBytesBE Solidity.Source.wordBytes amt) := by
  simp only [abiEncodeValues?, abiEncodeValuesAux?, show Ty.address.isDynamicAbi = false from rfl,
    show Ty.uint256.isDynamicAbi = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show Ty.listAbiHeadWords? [Ty.address, Ty.uint256] = some 2 from rfl, Option.bind_eq_bind, Option.bind_some]
  simp only [abiEncodeStaticValue?, abiStaticBytes?]
  have hf : abiAddressFits dst = true := by
    simp only [abiAddressFits, SolidCore.Solidity.Shared.norm]
    have h1 : dst % SolidCore.Solidity.Shared.wordModulus = dst :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le hd (by decide))
    exact decide_eq_true (by rw [h1]; exact hd)
  rw [if_pos hf]
  simp only [List.append_nil]

theorem payEnc (n : Nat) (ctx : Context) (rt : Runtime) (dst amt : Nat) (hd : dst < 2 ^ 160)
    (ha : amt < 2 ^ 256)
    (hb1 : rt.lookupStorageBase? "to" = none) (hl1 : rt.lookupLocal? "to" = some (.word dst))
    (hb2 : rt.lookupStorageBase? "amount" = none) (hl2 : rt.lookupLocal? "amount" = some (.word amt)) :
    Expr.evalFuel (n + 6) ctx rt (Expr.encode (EncodeKind.withSelector) (some transferSelE) [] [Ty.address, Ty.uint256]
      [Expr.var "to", Expr.var "amount"]) = pure (.bytes (payInput dst amt), rt) := by
  rw [Expr.evalFuel]
  simp only [Expr.evalListFuel]
  rw [selF, sbind_pure, show n + 3 = (n + 2) + 1 from rfl, varF _ _ _ _ _ hb1 hl1, sbind_pure,
    show n + 2 = (n + 1) + 1 from rfl, varF _ _ _ _ _ hb2 hl2, sbind_pure]
  simp only [sbind_pure, Value.expectWord, liftM, monadLift, MonadLift.monadLift, SolI.ofExcept]
  simp only [Runtime.materializeForValueUseList, mat_word, bind, Except.bind, dbind, pure]
  rw [enc2 dst amt hd ha]
  simp only [selBytes_eq', payInput, List.append_assoc]

/-- The low-level call pay makes. -/
def payCallE : Expr :=
  Expr.lowLevelCall (SolidCore.Solidity.Shared.Call.ExternalCallKind.call)
    (Expr.storageRead (StorageReadMode.ref) "token" [])
    (Expr.encode (EncodeKind.withSelector) (some transferSelE) [] [Ty.address, Ty.uint256]
      [Expr.var "to", Expr.var "amount"])
    (Expr.word 0) none false

/-- pay's require condition. -/
def payCond : Expr :=
  Expr.binary BinaryOp.boolAnd (Expr.var "ok")
    (Expr.binary BinaryOp.boolOr
      (Expr.binary BinaryOp.eq (Expr.castOp CastKind.uintCleanup 256 (Expr.length (Expr.var "ret")))
        (Expr.word 0))
      (Expr.abiDecode [Ty.bool] [AbiCleanup.none] (Expr.var "ret")))

/-- The inner block of pay. -/
def payInner : List Stmt :=
  [Stmt.varDecl Ty.bool "ok" none,
   Stmt.memoryVarDecl Ty.bytesCalldata "ret" none,
   Stmt.varDecl (Ty.tuple [Ty.bool, Ty.bytesCalldata]) "__solidcore_low_level_return" (some payCallE),
   Stmt.assignTuple [some (LValue.var "ok"), some (LValue.var "ret")] (Expr.var "__solidcore_low_level_return"),
   Stmt.requireStmt payCond (some "TRANSFER_FAILED")]

/-- pay's body, as the checker lowers it. -/
def payBody : Stmt :=
  Stmt.block [Stmt.skip,
    Stmt.assign (LValue.var "amount") (Expr.castOp CastKind.uintCleanup 256 (Expr.var "amount")),
    Stmt.block payInner]

theorem eval_skip (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime) :
    Stmt.eval (n + 1) tbl ctx rt .skip = pure (Result.normal rt) := by
  rw [Stmt.eval]

theorem eval_varDecl_some (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime)
    (ty : Ty) (x : String) (e : Expr) :
    Stmt.eval (n + 1) tbl ctx rt (.varDecl ty x (some e)) =
      ((Expr.eval ctx rt e).caught >>= fun r =>
        match r with
        | Except.ok (value, runtime') =>
            match ty.coerceValue? value with
            | some coerced => pure (Result.normal (runtime'.declareLocal x coerced))
            | none => pure (Result.reverted rt RevertData.typeMismatch)
        | Except.error err => pure (Result.reverted rt err)) := by
  rw [Stmt.eval]; dsimp only; rfl

theorem eval_memoryVarDecl_none (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime)
    (ty : Ty) (x : String) :
    Stmt.eval (n + 1) tbl ctx rt (.memoryVarDecl ty x none) =
      match rt.declareMemoryLocal ty x ty.defaultValue with
      | some updated => pure (Result.normal updated)
      | none => pure (Result.reverted rt RevertData.typeMismatch) := by
  rw [Stmt.eval]; dsimp only; rfl

theorem eval_require (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime)
    (c : Expr) (m : Option String) :
    Stmt.eval (n + 1) tbl ctx rt (.requireStmt c m) =
      ((Expr.eval ctx rt c).caught >>= fun r =>
        match r with
        | Except.ok (value, runtime') =>
            match value.expectWord with
            | Except.ok word =>
                if wordTruthy word then pure (Result.normal runtime')
                else match m with
                  | some message => pure (Result.reverted runtime' (RevertData.error message))
                  | none => pure (Result.reverted runtime' RevertData.empty)
            | Except.error err => pure (Result.reverted runtime' err)
        | Except.error err => pure (Result.reverted rt err)) := by
  rw [Stmt.eval]; dsimp only; rfl

theorem eval_assign_var (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime)
    (x : String) (e : Expr) :
    Stmt.eval (n + 1) tbl ctx rt (.assign (.var x) e) = Stmt.eval (n + 1) tbl ctx rt (.assign (.var x) e) := rfl


theorem cleanup256 (c : Bool) (w : Nat) (hw : w < 2 ^ 256) :
    uintCleanup? c 256 (.word w) = .ok (.word w) := by
  have hn : SolidCore.Solidity.Shared.norm w = w := Nat.mod_eq_of_lt hw
  have h2 : w < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := hw
  simp [uintCleanup?, Value.forceAbiLazy, Value.asStorageWord?, uintCast?, hn, bind, Except.bind,
    Nat.not_le.mpr h2, Nat.mod_eq_of_lt h2]

theorem castVar_eval (ctx : Context) (rt : Runtime) (x : String) (w : Nat) (hw : w < 2 ^ 256)
    (hb : rt.lookupStorageBase? x = none) (hl : rt.lookupLocal? x = some (.word w)) :
    Expr.eval ctx rt (Expr.castOp CastKind.uintCleanup 256 (Expr.var x)) =
      EvmCompiler.Simulation.Interaction.done (.ok (.word w, rt)) := by
  simp only [Expr.eval, Expr.orderFuel]
  rw [Expr.evalFuel]
  rw [show 0 + 1 + (0 + 1) = 1 + 1 from rfl, varF 1 ctx rt x w hb hl, sbind_pure]
  simp only [liftM, monadLift, MonadLift.monadLift, SolI.ofExcept, cleanup256 _ w hw]
  rfl

theorem resolve_var (ctx : Context) (rt : Runtime) (x : String) (v : Value)
    (hb : rt.lookupStorageBase? x = none) (hl : rt.lookupLocal? x = some v) :
    (LValue.var x).resolveWithRuntime ctx rt =
      EvmCompiler.Simulation.Interaction.done (.ok (.local x, rt)) := by
  simp only [LValue.resolveWithRuntime, LValue.toExpr, Expr.resolveLValue, Expr.orderFuel]
  rw [Expr.resolveLValueFuel]
  simp only [hb, hl]
  rfl

theorem pay_amount (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime) (dst amt : Nat)
    (ha : amt < 2 ^ 256)
    (hl : rt.locals = [[], [("to", .word dst), ("amount", .word amt)]]) :
    Stmt.eval (n + 1) tbl ctx rt
      (Stmt.assign (LValue.var "amount") (Expr.castOp CastKind.uintCleanup 256 (Expr.var "amount"))) =
      pure (Result.normal { rt with locals := [[], [("to", .word dst), ("amount", .word amt)]] }) := by
  rw [Stmt.eval]; dsimp only
  simp [LValue.wantsMemoryRefRhs, Runtime.lookupMemoryRef?, Runtime.lookupLocal?, hl, LocalEnv.lookup?,
    Frame.lookup?]
  rw [castVar_eval ctx rt "amount" amt ha (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, hl, LocalEnv.lookup?, Frame.lookup?])
    (by simp [Runtime.lookupLocal?, hl, LocalEnv.lookup?, Frame.lookup?])]
  have hr := resolve_var ctx rt "amount" (.word amt)
    (by simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, hl, LocalEnv.lookup?, Frame.lookup?])
    (by simp [Runtime.lookupLocal?, hl, LocalEnv.lookup?, Frame.lookup?])
  simp only [caught_done_ok, bind_done_ok, hr]
  simp [ResolvedLValue.write, Runtime.assignLocal?, Runtime.lookupLocal?, hl, LocalEnv.lookup?,
    Frame.lookup?, LocalEnv.assign?, Value.coerceLike?, Frame.assign?]
  done

/-- The runtime after bytes memory ret. -/
def retRt (rt : Runtime) : Runtime :=
  { state := rt.state
    locals := rt.locals.declare "ret" (Value.memoryRef rt.nextMemory)
    memory := rt.memory.insertLoop rt.nextMemory (Value.bytes [])
    nextMemory := rt.nextMemory + 1
    nextMemoryByte := rt.nextMemoryByte + (Value.bytes []).memoryAllocationBytes }

theorem ret_decl (rt : Runtime) :
    rt.declareMemoryLocal Ty.bytesCalldata "ret" Ty.bytesCalldata.defaultValue =
      some (retRt rt) := by
  simp [Runtime.declareMemoryLocal, Ty.defaultValue, Ty.coerceValue?, Runtime.memoryStoredValue,
    Runtime.allocMemory, Runtime.declareLocal, retRt]

theorem tokF (n : Nat) (ctx : Context) (rt : Runtime) (hf : AddrFieldOk ctx "token" tokenField)
    (hw : rt.state.loadSlot tokenField.slot < Generic.wordSize) :
    Expr.evalFuel (n + 1) ctx rt (Expr.storageRead .ref "token" []) =
      pure (.word (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20), rt) := by
  simp only [Expr.evalFuel]
  simp only [load_addrField hf hw]
  rfl


theorem tokF' (n : Nat) (ctx : Context) (rt' rt : Runtime) (hf : AddrFieldOk ctx "token" tokenField)
    (hs : rt'.state = rt.state) (hw : rt.state.loadSlot tokenField.slot < Generic.wordSize) :
    Expr.evalFuel (n + 1) ctx rt' (Expr.storageRead .ref "token" []) =
      pure (.word (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20), rt') := by
  rw [← hs]; exact tokF n ctx rt' hf (hs ▸ hw)

theorem caught_request {α : Type} (q : EvmCompiler.Simulation.Query)
    (k : EvmCompiler.Simulation.Answer q → SolI α) :
    SolI.caught (EvmCompiler.Simulation.Interaction.request q k) =
      EvmCompiler.Simulation.Interaction.request q (fun a => SolI.caught (k a)) := rfl

theorem ipure_eq {α : Type} (x : α) :
    (EvmCompiler.Simulation.Interaction.pure x : SolI α) = EvmCompiler.Simulation.Interaction.done (.ok x) := rfl

theorem word0F (m : Nat) (ctx : Context) (rt : Runtime) :
    Expr.evalFuel (m + 1) ctx rt (Expr.word 0) = pure (.word 0, rt) := by
  rw [Expr.evalFuel]
  rfl

set_option maxHeartbeats 300000 in
theorem pay_req (n : Nat) (tbl : FunctionTable) (ctx : Context) (rt : Runtime) (dst amt : Nat)
    (hd : dst < 2 ^ 160) (ha : amt < 2 ^ 256)
    (hl : rt.locals = [[("to", .word dst), ("amount", .word amt)]])
    (hf : AddrFieldOk ctx "token" tokenField) (hw : rt.state.loadSlot tokenField.slot < Generic.wordSize)
    (hcons : ctx.construction = false)
    (hself : wordEq (SolidCore.Solidity.Shared.norm (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20)) ctx.self = false) :
    ∃ k, Stmt.eval (n + 3) tbl ctx rt payBody =
      .request (.external (snapshotWorld ctx rt.state)
        (.call (buildCallRequest ctx .call (SolidCore.Solidity.Shared.norm (fieldValue (rt.state.loadSlot tokenField.slot) tokenField.packedOffset 20))
          (List.map normByte (payInput dst amt)) (SolidCore.Solidity.Shared.norm 0) none))) k := by
  rw [payBody, eval_block, evalList_cons, show n + 2 = (n + 1) + 1 from rfl, eval_skip, sbind_pure]
  dsimp only
  rw [evalList_cons, pay_amount (n + 1) tbl ctx rt.pushScope dst amt ha (by simp [Runtime.pushScope, hl]), sbind_pure]
  dsimp only
  rw [evalList_cons, eval_block, payInner, evalList_cons, eval_varDecl_none, sbind_pure]
  dsimp only
  rw [evalList_cons, eval_memoryVarDecl_none, ret_decl]
  dsimp only
  rw [sbind_pure]
  dsimp only
  rw [evalList_cons, eval_varDecl_some]
  rw [Expr.eval, show payCallE.orderFuel + 1 = 13 + 1 from rfl, payCallE,
    eval_lowLevelCall 13 ctx _ _ _ _ false (tokF' 12 ctx _ rt hf ?hs hw) rfl (word0F 12 ctx _) rfl
      (payEnc 7 ctx _ dst amt hd ha ?b1 ?l1 ?b2 ?l2) rfl hcons hself]
  · simp only [caught_request, bind_request]
    exact ⟨_, rfl⟩
  · rfl
  all_goals simp [Runtime.lookupStorageBase?, Runtime.lookupLocal?, retRt, Runtime.declareLocal, Runtime.pushScope,
    LocalEnv.declare, LocalEnv.lookup?, Frame.lookup?]

/-- info: 'SolidCore.Refinement.CallFamilies.pay_req' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pay_req

end SolidCore.Refinement.CallFamilies
