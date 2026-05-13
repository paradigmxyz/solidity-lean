import SharedSemantics.Word
import SolidCore.Spine.L03_GeneratedYul.Interface
import SolidCore.Spine.L04_StackCfg.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P04_GeneratedYulToStackCfg

structure Artifact where
  program : L04_StackCfg.Program
  wf : L04_StackCfg.WF program

theorem Artifact.ext_program {left right : Artifact}
    (hProgram : left.program = right.program) :
    left = right := by
  cases left with
  | mk leftProgram leftWf =>
      cases right with
      | mk rightProgram rightWf =>
          dsimp at hProgram
          cases hProgram
          have hWf : leftWf = rightWf := Subsingleton.elim _ _
          cases hWf
          rfl

def Artifact.stop : Artifact :=
  { program := L04_StackCfg.Program.stop
    wf := L04_StackCfg.Program.stop_wf }

def Artifact.returnCode (code : List L04_StackCfg.Instr)
    (hPseudoFree : L04_StackCfg.InstrsPseudoFree code)
    (hStackDepth : L04_StackCfg.stackDepthAfter? 0 code = some 1) :
    Artifact :=
  { program := L04_StackCfg.Program.returnCode code
    wf := L04_StackCfg.Program.returnCode_wf hPseudoFree hStackDepth }

def Artifact.jumpReturnCode (code : List L04_StackCfg.Instr)
    (hPseudoFree : L04_StackCfg.InstrsPseudoFree code)
    (hStackDepth : L04_StackCfg.stackDepthAfter? 0 code = some 1) :
    Artifact :=
  { program := L04_StackCfg.Program.jumpReturnCode code
    wf := L04_StackCfg.Program.jumpReturnCode_wf hPseudoFree hStackDepth }

def Artifact.returnWord (value : L03_GeneratedYul.Word) : Artifact :=
  Artifact.returnCode [L04_StackCfg.Instr.push (L04_StackCfg.Atom.word value)]
    (L04_StackCfg.InstrsPseudoFree_singleton_push
      (L04_StackCfg.Atom.word value))
    (by
      simpa using
        L04_StackCfg.stackDepthAfter?_singleton_push
          (L04_StackCfg.Atom.word value) 0)

structure CheckedExpr (source : L03_GeneratedYul.Expr) where
  code : List L04_StackCfg.Instr
  value : L03_GeneratedYul.Word
  eval : source.Eval value
  pseudoFree : L04_StackCfg.InstrsPseudoFree code
  stackDepth :
    ∀ depth : Nat,
      L04_StackCfg.stackDepthAfter? depth code = some (depth + 1)
  exec :
    ∀ stack : List L04_StackCfg.Word,
      L04_StackCfg.execInstrs stack code = some (value :: stack)

structure CheckedDiscardedExpr (source : L03_GeneratedYul.Expr) where
  code : List L04_StackCfg.Instr
  value : L03_GeneratedYul.Word
  eval : source.Eval value
  pseudoFree : L04_StackCfg.InstrsPseudoFree code
  stackDepth :
    ∀ depth : Nat,
      L04_StackCfg.stackDepthAfter? depth code = some depth
  exec :
    ∀ stack : List L04_StackCfg.Word,
      L04_StackCfg.execInstrs stack code = some stack

structure CheckedNeutralStmt (source : L03_GeneratedYul.Stmt) where
  code : List L04_StackCfg.Instr
  sourceNeutral : source.neutral? = true
  pseudoFree : L04_StackCfg.InstrsPseudoFree code
  stackDepth :
    ∀ depth : Nat,
      L04_StackCfg.stackDepthAfter? depth code = some depth
  exec :
    ∀ stack : List L04_StackCfg.Word,
      L04_StackCfg.execInstrs stack code = some stack

structure CheckedNeutralStmts (source : List L03_GeneratedYul.Stmt) where
  code : List L04_StackCfg.Instr
  sourceNeutral : L03_GeneratedYul.Stmt.neutralStmts? source = true
  pseudoFree : L04_StackCfg.InstrsPseudoFree code
  stackDepth :
    ∀ depth : Nat,
      L04_StackCfg.stackDepthAfter? depth code = some depth
  exec :
    ∀ stack : List L04_StackCfg.Word,
      L04_StackCfg.execInstrs stack code = some stack

structure CheckedReturnStmts (source : List L03_GeneratedYul.Stmt) where
  code : List L04_StackCfg.Instr
  value : L03_GeneratedYul.Word
  sourceReturn :
    ∃ expr,
      (L03_GeneratedYul.Stmt.block source).returnedExpr? = some expr ∧
        expr.Eval value
  pseudoFree : L04_StackCfg.InstrsPseudoFree code
  stackDepth :
    L04_StackCfg.stackDepthAfter? 0 code = some 1
  exec :
    L04_StackCfg.execInstrs [] code = some [value]

def CheckedExpr.word (value : L03_GeneratedYul.Word) :
    CheckedExpr (L03_GeneratedYul.Expr.word value) :=
  { code :=
      [L04_StackCfg.Instr.push
        (L04_StackCfg.Atom.word (SharedSemantics.norm value))]
    value := SharedSemantics.norm value
    eval := L03_GeneratedYul.Expr.word_eval_norm value
    pseudoFree :=
      L04_StackCfg.InstrsPseudoFree_singleton_push
        (L04_StackCfg.Atom.word (SharedSemantics.norm value))
    stackDepth := by
      intro depth
      exact
        L04_StackCfg.stackDepthAfter?_singleton_push
          (L04_StackCfg.Atom.word (SharedSemantics.norm value)) depth
    exec := by
      intro stack
      simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr] }

def CheckedExpr.word0 : CheckedExpr L03_GeneratedYul.Expr.word0 :=
  CheckedExpr.word 0

def CheckedExpr.word3 : CheckedExpr L03_GeneratedYul.Expr.word3 :=
  CheckedExpr.word 3

def CheckedExpr.add {lhs rhs : L03_GeneratedYul.Expr}
    (lhsChecked : CheckedExpr lhs) (rhsChecked : CheckedExpr rhs)
    (hEval :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.add [lhs, rhs]).Eval
        (SharedSemantics.addWord lhsChecked.value rhsChecked.value)) :
    CheckedExpr
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.add [lhs, rhs]) :=
  { code :=
      lhsChecked.code ++ (rhsChecked.code ++
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add]
      )
    value := SharedSemantics.addWord lhsChecked.value rhsChecked.value
    eval := hEval
    pseudoFree :=
      L04_StackCfg.InstrsPseudoFree_append lhsChecked.pseudoFree
        (L04_StackCfg.InstrsPseudoFree_append rhsChecked.pseudoFree
          (L04_StackCfg.InstrsPseudoFree_singleton_op
            L04_StackCfg.PrimOp.add))
    stackDepth := by
      intro depth
      rw [L04_StackCfg.stackDepthAfter?_append
        lhsChecked.code
        (rhsChecked.code ++
          [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add]) depth]
      simp [lhsChecked.stackDepth depth]
      rw [L04_StackCfg.stackDepthAfter?_append
        rhsChecked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add]
        (depth + 1)]
      simp [rhsChecked.stackDepth (depth + 1)]
      simpa [Nat.add_assoc] using
        L04_StackCfg.stackDepthAfter?_singleton_add depth
    exec := by
      intro stack
      rw [L04_StackCfg.execInstrs_append
        lhsChecked.code
        (rhsChecked.code ++
          [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add]) stack]
      simp [lhsChecked.exec stack]
      rw [L04_StackCfg.execInstrs_append
        rhsChecked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add]
        (lhsChecked.value :: stack)]
      simp [rhsChecked.exec (lhsChecked.value :: stack),
        L04_StackCfg.execInstrs, L04_StackCfg.execInstr] }

def CheckedExpr.mul {lhs rhs : L03_GeneratedYul.Expr}
    (lhsChecked : CheckedExpr lhs) (rhsChecked : CheckedExpr rhs)
    (hEval :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.mul [lhs, rhs]).Eval
        (SharedSemantics.mulWord lhsChecked.value rhsChecked.value)) :
    CheckedExpr
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.mul [lhs, rhs]) :=
  { code :=
      lhsChecked.code ++ (rhsChecked.code ++
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.mul]
      )
    value := SharedSemantics.mulWord lhsChecked.value rhsChecked.value
    eval := hEval
    pseudoFree :=
      L04_StackCfg.InstrsPseudoFree_append lhsChecked.pseudoFree
        (L04_StackCfg.InstrsPseudoFree_append rhsChecked.pseudoFree
          (L04_StackCfg.InstrsPseudoFree_singleton_op
            L04_StackCfg.PrimOp.mul))
    stackDepth := by
      intro depth
      rw [L04_StackCfg.stackDepthAfter?_append
        lhsChecked.code
        (rhsChecked.code ++
          [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.mul]) depth]
      simp [lhsChecked.stackDepth depth]
      rw [L04_StackCfg.stackDepthAfter?_append
        rhsChecked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.mul]
        (depth + 1)]
      simp [rhsChecked.stackDepth (depth + 1)]
      simpa [Nat.add_assoc] using
        L04_StackCfg.stackDepthAfter?_singleton_mul depth
    exec := by
      intro stack
      rw [L04_StackCfg.execInstrs_append
        lhsChecked.code
        (rhsChecked.code ++
          [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.mul]) stack]
      simp [lhsChecked.exec stack]
      rw [L04_StackCfg.execInstrs_append
        rhsChecked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.mul]
        (lhsChecked.value :: stack)]
      simp [rhsChecked.exec (lhsChecked.value :: stack),
        L04_StackCfg.execInstrs, L04_StackCfg.execInstr] }

def CheckedExpr.sub {lhs rhs : L03_GeneratedYul.Expr}
    (lhsChecked : CheckedExpr lhs) (rhsChecked : CheckedExpr rhs)
    (hEval :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.sub [lhs, rhs]).Eval
        (SharedSemantics.subWord lhsChecked.value rhsChecked.value)) :
    CheckedExpr
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.sub [lhs, rhs]) :=
  { code :=
      lhsChecked.code ++ (rhsChecked.code ++
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.sub]
      )
    value := SharedSemantics.subWord lhsChecked.value rhsChecked.value
    eval := hEval
    pseudoFree :=
      L04_StackCfg.InstrsPseudoFree_append lhsChecked.pseudoFree
        (L04_StackCfg.InstrsPseudoFree_append rhsChecked.pseudoFree
          (L04_StackCfg.InstrsPseudoFree_singleton_op
            L04_StackCfg.PrimOp.sub))
    stackDepth := by
      intro depth
      rw [L04_StackCfg.stackDepthAfter?_append
        lhsChecked.code
        (rhsChecked.code ++
          [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.sub]) depth]
      simp [lhsChecked.stackDepth depth]
      rw [L04_StackCfg.stackDepthAfter?_append
        rhsChecked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.sub]
        (depth + 1)]
      simp [rhsChecked.stackDepth (depth + 1)]
      simpa [Nat.add_assoc] using
        L04_StackCfg.stackDepthAfter?_singleton_sub depth
    exec := by
      intro stack
      rw [L04_StackCfg.execInstrs_append
        lhsChecked.code
        (rhsChecked.code ++
          [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.sub]) stack]
      simp [lhsChecked.exec stack]
      rw [L04_StackCfg.execInstrs_append
        rhsChecked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.sub]
        (lhsChecked.value :: stack)]
      simp [rhsChecked.exec (lhsChecked.value :: stack),
        L04_StackCfg.execInstrs, L04_StackCfg.execInstr] }

def CheckedExpr.iszero {source : L03_GeneratedYul.Expr}
    (checked : CheckedExpr source)
    (hEval :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.iszero [source]).Eval
        (SharedSemantics.iszeroWord checked.value)) :
    CheckedExpr
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.iszero [source]) :=
  { code := checked.code ++
      [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.iszero]
    value := SharedSemantics.iszeroWord checked.value
    eval := hEval
    pseudoFree :=
      L04_StackCfg.InstrsPseudoFree_append checked.pseudoFree
        (L04_StackCfg.InstrsPseudoFree_singleton_op
          L04_StackCfg.PrimOp.iszero)
    stackDepth := by
      intro depth
      rw [L04_StackCfg.stackDepthAfter?_append
        checked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.iszero] depth]
      simp [checked.stackDepth depth]
      simpa using
        L04_StackCfg.stackDepthAfter?_singleton_iszero depth
    exec := by
      intro stack
      rw [L04_StackCfg.execInstrs_append
        checked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.iszero] stack]
      simp [checked.exec stack, L04_StackCfg.execInstrs,
        L04_StackCfg.execInstr] }

def CheckedExpr.eqOp {lhs rhs : L03_GeneratedYul.Expr}
    (lhsChecked : CheckedExpr lhs) (rhsChecked : CheckedExpr rhs)
    (hEval :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.eqOp [lhs, rhs]).Eval
        (SharedSemantics.eqWord lhsChecked.value rhsChecked.value)) :
    CheckedExpr
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.eqOp [lhs, rhs]) :=
  { code :=
      lhsChecked.code ++ (rhsChecked.code ++
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.eq]
      )
    value := SharedSemantics.eqWord lhsChecked.value rhsChecked.value
    eval := hEval
    pseudoFree :=
      L04_StackCfg.InstrsPseudoFree_append lhsChecked.pseudoFree
        (L04_StackCfg.InstrsPseudoFree_append rhsChecked.pseudoFree
          (L04_StackCfg.InstrsPseudoFree_singleton_op
            L04_StackCfg.PrimOp.eq))
    stackDepth := by
      intro depth
      rw [L04_StackCfg.stackDepthAfter?_append
        lhsChecked.code
        (rhsChecked.code ++
          [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.eq]) depth]
      simp [lhsChecked.stackDepth depth]
      rw [L04_StackCfg.stackDepthAfter?_append
        rhsChecked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.eq]
        (depth + 1)]
      simp [rhsChecked.stackDepth (depth + 1)]
      simpa [Nat.add_assoc] using
        L04_StackCfg.stackDepthAfter?_singleton_eq depth
    exec := by
      intro stack
      rw [L04_StackCfg.execInstrs_append
        lhsChecked.code
        (rhsChecked.code ++
          [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.eq]) stack]
      simp [lhsChecked.exec stack]
      rw [L04_StackCfg.execInstrs_append
        rhsChecked.code
        [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.eq]
        (lhsChecked.value :: stack)]
      simp [rhsChecked.exec (lhsChecked.value :: stack),
        L04_StackCfg.execInstrs, L04_StackCfg.execInstr] }

def CheckedExpr.addCodePseudoFree
    {lhs rhs : L03_GeneratedYul.Expr}
    (lhsChecked : CheckedExpr lhs) (rhsChecked : CheckedExpr rhs) :
    L04_StackCfg.InstrsPseudoFree
      (lhsChecked.code ++
        (rhsChecked.code ++ [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add])) :=
  L04_StackCfg.InstrsPseudoFree_append lhsChecked.pseudoFree
    (L04_StackCfg.InstrsPseudoFree_append rhsChecked.pseudoFree
      (L04_StackCfg.InstrsPseudoFree_singleton_op L04_StackCfg.PrimOp.add))

def CheckedDiscardedExpr.ofChecked {source : L03_GeneratedYul.Expr}
    (checked : CheckedExpr source) : CheckedDiscardedExpr source :=
  { code := checked.code ++ [L04_StackCfg.Instr.pop]
    value := checked.value
    eval := checked.eval
    pseudoFree :=
      L04_StackCfg.InstrsPseudoFree_append checked.pseudoFree
        L04_StackCfg.InstrsPseudoFree_singleton_pop
    stackDepth := by
      intro depth
      rw [L04_StackCfg.stackDepthAfter?_append
        checked.code [L04_StackCfg.Instr.pop] depth]
      simp [checked.stackDepth depth]
      simpa using L04_StackCfg.stackDepthAfter?_singleton_pop depth
    exec := by
      intro stack
      rw [L04_StackCfg.execInstrs_append
        checked.code [L04_StackCfg.Instr.pop] stack]
      simp [checked.exec stack, L04_StackCfg.execInstrs,
        L04_StackCfg.execInstr] }

def CheckedNeutralStmt.skip :
    CheckedNeutralStmt L03_GeneratedYul.Stmt.skip :=
  { code := []
    sourceNeutral := rfl
    pseudoFree := L04_StackCfg.InstrsPseudoFree_nil
    stackDepth := by
      intro depth
      rfl
    exec := by
      intro stack
      rfl }

def CheckedNeutralStmt.expr {source : L03_GeneratedYul.Expr}
    (checked : CheckedDiscardedExpr source) :
    CheckedNeutralStmt (L03_GeneratedYul.Stmt.expr source) :=
  { code := checked.code
    sourceNeutral := by
      have hEval : source.eval? = some checked.value := by
        simpa [L03_GeneratedYul.Expr.Eval] using checked.eval
      simp [L03_GeneratedYul.Stmt.neutral?, hEval]
    pseudoFree := checked.pseudoFree
    stackDepth := checked.stackDepth
    exec := checked.exec }

def CheckedNeutralStmts.nil :
    CheckedNeutralStmts [] :=
  { code := []
    sourceNeutral := rfl
    pseudoFree := L04_StackCfg.InstrsPseudoFree_nil
    stackDepth := by
      intro depth
      rfl
    exec := by
      intro stack
      rfl }

def CheckedNeutralStmts.cons
    {stmt : L03_GeneratedYul.Stmt} {rest : List L03_GeneratedYul.Stmt}
    (head : CheckedNeutralStmt stmt)
    (tail : CheckedNeutralStmts rest) :
    CheckedNeutralStmts (stmt :: rest) :=
  { code := head.code ++ tail.code
    sourceNeutral := by
      simp [L03_GeneratedYul.Stmt.neutralStmts?,
        head.sourceNeutral, tail.sourceNeutral]
    pseudoFree :=
      L04_StackCfg.InstrsPseudoFree_append
        head.pseudoFree tail.pseudoFree
    stackDepth := by
      intro depth
      rw [L04_StackCfg.stackDepthAfter?_append]
      simp [head.stackDepth depth, tail.stackDepth depth]
    exec := by
      intro stack
      rw [L04_StackCfg.execInstrs_append]
      simp [head.exec stack, tail.exec stack] }

def CheckedNeutralStmt.block {stmts : List L03_GeneratedYul.Stmt}
    (checked : CheckedNeutralStmts stmts) :
    CheckedNeutralStmt (L03_GeneratedYul.Stmt.block stmts) :=
  { code := checked.code
    sourceNeutral := by
      simpa [L03_GeneratedYul.Stmt.neutral?] using checked.sourceNeutral
    pseudoFree := checked.pseudoFree
    stackDepth := checked.stackDepth
    exec := checked.exec }

def CheckedReturnStmts.returnedBlock
    {source : List L03_GeneratedYul.Stmt}
    {expr : L03_GeneratedYul.Expr}
    (hReturned :
      (L03_GeneratedYul.Stmt.block source).returnedExpr? = some expr)
    (checked : CheckedExpr expr) :
    CheckedReturnStmts source :=
  { code := checked.code
    value := checked.value
    sourceReturn := by
      exact ⟨expr, hReturned, checked.eval⟩
    pseudoFree := checked.pseudoFree
    stackDepth := checked.stackDepth 0
    exec := by
      simpa using checked.exec [] }

def CheckedReturnStmts.returned
    {stmt : L03_GeneratedYul.Stmt}
    {expr : L03_GeneratedYul.Expr}
    (hReturned : stmt.returnedExpr? = some expr)
    (checked : CheckedExpr expr) :
    CheckedReturnStmts [stmt] :=
  CheckedReturnStmts.returnedBlock
    (source := [stmt])
    (by
      simp [L03_GeneratedYul.Stmt.returnedExpr?,
        L03_GeneratedYul.Stmt.returnedExprs?, hReturned])
    checked

theorem CheckedReturnStmts.returned_proof_irrel
    {stmt : L03_GeneratedYul.Stmt}
    {expr : L03_GeneratedYul.Expr}
    {hLeft hRight : stmt.returnedExpr? = some expr}
    (checked : CheckedExpr expr) :
    CheckedReturnStmts.returned hLeft checked =
      CheckedReturnStmts.returned hRight checked := by
  have hProof : hLeft = hRight := Subsingleton.elim _ _
  cases hProof
  rfl

def CheckedReturnStmts.cons
    {stmt : L03_GeneratedYul.Stmt} {rest : List L03_GeneratedYul.Stmt}
    (head : CheckedNeutralStmt stmt)
    (tail : CheckedReturnStmts rest) :
    CheckedReturnStmts (stmt :: rest) :=
  { code := head.code ++ tail.code
    value := tail.value
    sourceReturn := by
      rcases tail.sourceReturn with ⟨expr, hReturned, hEval⟩
      refine ⟨expr, ?_, hEval⟩
      cases rest with
      | nil =>
          simp [L03_GeneratedYul.Stmt.returnedExpr?,
            L03_GeneratedYul.Stmt.returnedExprs?] at hReturned
      | cons next rest' =>
          have hTail :
              L03_GeneratedYul.Stmt.returnedExprs? (next :: rest') =
                some expr := by
            simpa [L03_GeneratedYul.Stmt.returnedExpr?] using hReturned
          simp [L03_GeneratedYul.Stmt.returnedExpr?,
            L03_GeneratedYul.Stmt.returnedExprs?,
            head.sourceNeutral, hTail]
    pseudoFree :=
      L04_StackCfg.InstrsPseudoFree_append
        head.pseudoFree tail.pseudoFree
    stackDepth := by
      rw [L04_StackCfg.stackDepthAfter?_append]
      simp [head.stackDepth 0, tail.stackDepth]
    exec := by
      rw [L04_StackCfg.execInstrs_append]
      simp [head.exec [], tail.exec] }

def Artifact.returnStmtsChecked
    {source : List L03_GeneratedYul.Stmt}
    (checked : CheckedReturnStmts source) : Artifact :=
  Artifact.returnCode checked.code checked.pseudoFree checked.stackDepth

theorem Artifact.returnStmtsChecked_semantics
    {source : List L03_GeneratedYul.Stmt}
    (checked : CheckedReturnStmts source) :
    L04_StackCfg.Semantics
      (Artifact.returnStmtsChecked checked).program
      (L01_ValidSolidity.Behavior.returnedWord checked.value) := by
  simpa [Artifact.returnStmtsChecked, Artifact.returnCode] using
    L04_StackCfg.Program.returnCode_semantics
      (code := checked.code)
      (value := checked.value)
      (stack := [])
      checked.exec

theorem CheckedReturnStmts.source_semantics
    {source : List L03_GeneratedYul.Stmt}
    (checked : CheckedReturnStmts source) :
    L03_GeneratedYul.Semantics
      (L03_GeneratedYul.Program.returnStmt
        (L03_GeneratedYul.Stmt.block source))
      (L01_ValidSolidity.Behavior.returnedWord checked.value) := by
  rcases checked.sourceReturn with ⟨expr, hReturned, hEval⟩
  exact L03_GeneratedYul.Program.returnStmt_semantics hReturned hEval

def pushPushAddPseudoFree
    (lhs rhs : L04_StackCfg.Atom) :
    L04_StackCfg.InstrsPseudoFree
      [ L04_StackCfg.Instr.push lhs
      , L04_StackCfg.Instr.push rhs
      , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ] :=
  L04_StackCfg.InstrsPseudoFree_append
    (L04_StackCfg.InstrsPseudoFree_singleton_push lhs)
    (L04_StackCfg.InstrsPseudoFree_append
      (L04_StackCfg.InstrsPseudoFree_singleton_push rhs)
      (L04_StackCfg.InstrsPseudoFree_singleton_op L04_StackCfg.PrimOp.add))

def pushPushAddStackDepth
    (lhs rhs : L04_StackCfg.Atom) :
    L04_StackCfg.stackDepthAfter? 0
      [ L04_StackCfg.Instr.push lhs
      , L04_StackCfg.Instr.push rhs
      , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ] = some 1 := by
  simp [L04_StackCfg.stackDepthAfter?, L04_StackCfg.Instr.stackDepthAfter?]

def pushPushAddPushAddPseudoFree
    (lhs rhs extra : L04_StackCfg.Atom) :
    L04_StackCfg.InstrsPseudoFree
      [ L04_StackCfg.Instr.push lhs
      , L04_StackCfg.Instr.push rhs
      , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add
      , L04_StackCfg.Instr.push extra
      , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ] :=
  L04_StackCfg.InstrsPseudoFree_append
    (pushPushAddPseudoFree lhs rhs)
    (L04_StackCfg.InstrsPseudoFree_append
      (L04_StackCfg.InstrsPseudoFree_singleton_push extra)
      (L04_StackCfg.InstrsPseudoFree_singleton_op L04_StackCfg.PrimOp.add))

def pushPushAddPushAddStackDepth
    (lhs rhs extra : L04_StackCfg.Atom) :
    L04_StackCfg.stackDepthAfter? 0
      [ L04_StackCfg.Instr.push lhs
      , L04_StackCfg.Instr.push rhs
      , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add
      , L04_StackCfg.Instr.push extra
      , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ] = some 1 := by
  simp [L04_StackCfg.stackDepthAfter?, L04_StackCfg.Instr.stackDepthAfter?]

def Artifact.returnChecked {source : L03_GeneratedYul.Expr}
    (checked : CheckedExpr source) : Artifact :=
  Artifact.returnCode checked.code checked.pseudoFree (checked.stackDepth 0)

@[simp] theorem Artifact.returnStmtsChecked_returnedBlock
    {source : List L03_GeneratedYul.Stmt}
    {expr : L03_GeneratedYul.Expr}
    (hReturned :
      (L03_GeneratedYul.Stmt.block source).returnedExpr? = some expr)
    (checked : CheckedExpr expr) :
    Artifact.returnStmtsChecked
        (CheckedReturnStmts.returnedBlock hReturned checked) =
      Artifact.returnChecked checked := by
  apply Artifact.ext_program
  rfl

def Artifact.jumpReturnChecked {source : L03_GeneratedYul.Expr}
    (checked : CheckedExpr source) : Artifact :=
  Artifact.jumpReturnCode checked.code checked.pseudoFree (checked.stackDepth 0)

theorem Artifact.jumpReturnChecked_reaches
    {source : L03_GeneratedYul.Expr} (checked : CheckedExpr source) :
    L04_StackCfg.Reaches (Artifact.jumpReturnChecked checked).program
      (L04_StackCfg.Config.at
        (Artifact.jumpReturnChecked checked).program.entry [])
      (L04_StackCfg.Config.returnedWord checked.value) := by
  simpa [Artifact.jumpReturnChecked, Artifact.jumpReturnCode] using
    L04_StackCfg.Program.jumpReturnCode_reaches (checked.exec [])

def Artifact.neutralThenReturnChecked
    {prelude : List L03_GeneratedYul.Stmt}
    {source : L03_GeneratedYul.Expr}
    (neutral : CheckedNeutralStmts prelude)
    (checked : CheckedExpr source) : Artifact :=
  Artifact.returnCode (neutral.code ++ checked.code)
    (L04_StackCfg.InstrsPseudoFree_append
      neutral.pseudoFree checked.pseudoFree)
    (by
      rw [L04_StackCfg.stackDepthAfter?_append]
      simp [neutral.stackDepth 0, checked.stackDepth 0])

theorem Artifact.neutralThenReturnChecked_exec
    {prelude : List L03_GeneratedYul.Stmt}
    {source : L03_GeneratedYul.Expr}
    (neutral : CheckedNeutralStmts prelude)
    (checked : CheckedExpr source) :
    L04_StackCfg.execInstrs []
      (neutral.code ++ checked.code) =
        some [checked.value] := by
  rw [L04_StackCfg.execInstrs_append]
  simp [neutral.exec [], checked.exec []]

theorem Artifact.neutralThenReturnChecked_reaches
    {prelude : List L03_GeneratedYul.Stmt}
    {source : L03_GeneratedYul.Expr}
    (neutral : CheckedNeutralStmts prelude)
    (checked : CheckedExpr source) :
    L04_StackCfg.Reaches
      (Artifact.neutralThenReturnChecked neutral checked).program
      (L04_StackCfg.Config.at
        (Artifact.neutralThenReturnChecked neutral checked).program.entry [])
      (L04_StackCfg.Config.returnedWord checked.value) := by
  simpa [Artifact.neutralThenReturnChecked, Artifact.returnCode] using
    L04_StackCfg.Program.returnCode_reaches
      (code := neutral.code ++ checked.code)
      (value := checked.value)
      (stack := [])
      (Artifact.neutralThenReturnChecked_exec neutral checked)

theorem Artifact.neutralThenReturnChecked_semantics
    {prelude : List L03_GeneratedYul.Stmt}
    {source : L03_GeneratedYul.Expr}
    (neutral : CheckedNeutralStmts prelude)
    (checked : CheckedExpr source) :
    L04_StackCfg.Semantics
      (Artifact.neutralThenReturnChecked neutral checked).program
      (L01_ValidSolidity.Behavior.returnedWord checked.value) := by
  simpa [Artifact.neutralThenReturnChecked, Artifact.returnCode] using
    L04_StackCfg.Program.returnCode_semantics
      (code := neutral.code ++ checked.code)
      (value := checked.value)
      (stack := [])
      (Artifact.neutralThenReturnChecked_exec neutral checked)

def CheckedExpr.add1And2 :
    CheckedExpr L03_GeneratedYul.Expr.add1And2 := by
  simpa [L03_GeneratedYul.Expr.add1And2, L03_GeneratedYul.Expr.add,
    CheckedExpr.word, SharedSemantics.addWord, SharedSemantics.norm,
    SharedSemantics.wordModulus] using
    CheckedExpr.add (CheckedExpr.word 1) (CheckedExpr.word 2) (by rfl)

def compileExprChecked? :
    (source : L03_GeneratedYul.Expr) -> Option (CheckedExpr source)
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.add
      [lhs, rhs] =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
      let result :=
        SharedSemantics.addWord lhsChecked.value rhsChecked.value
      if hEval :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.add
              [lhs, rhs]).eval? = some result then
        some
          (CheckedExpr.add lhsChecked rhsChecked
            (by simpa [L03_GeneratedYul.Expr.Eval] using hEval))
      else
        none
      | _, _ => none
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.mul
      [lhs, rhs] =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
      let result :=
        SharedSemantics.mulWord lhsChecked.value rhsChecked.value
      if hEval :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.mul
              [lhs, rhs]).eval? = some result then
        some
          (CheckedExpr.mul lhsChecked rhsChecked
            (by simpa [L03_GeneratedYul.Expr.Eval] using hEval))
      else
        none
      | _, _ => none
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.sub
      [lhs, rhs] =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
      let result :=
        SharedSemantics.subWord lhsChecked.value rhsChecked.value
      if hEval :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.sub
              [lhs, rhs]).eval? = some result then
        some
          (CheckedExpr.sub lhsChecked rhsChecked
            (by simpa [L03_GeneratedYul.Expr.Eval] using hEval))
      else
        none
      | _, _ => none
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.iszero
      [source] =>
      match compileExprChecked? source with
      | some checked =>
      let result :=
        SharedSemantics.iszeroWord checked.value
      if hEval :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.iszero
              [source]).eval? = some result then
        some
          (CheckedExpr.iszero checked
            (by simpa [L03_GeneratedYul.Expr.Eval] using hEval))
      else
        none
      | none => none
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.eqOp
      [lhs, rhs] =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
      let result :=
        SharedSemantics.eqWord lhsChecked.value rhsChecked.value
      if hEval :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.eqOp
              [lhs, rhs]).eval? = some result then
        some
          (CheckedExpr.eqOp lhsChecked rhsChecked
            (by simpa [L03_GeneratedYul.Expr.Eval] using hEval))
      else
        none
      | _, _ => none
  | L03_GeneratedYul.Expr.word value =>
      some (CheckedExpr.word value)
  | _ => none

def compileExpr? (source : L03_GeneratedYul.Expr) :
    Option (List L04_StackCfg.Instr) :=
  match compileExprChecked? source with
  | some checked => some checked.code
  | none => none

def compileDiscardedExprChecked? (source : L03_GeneratedYul.Expr) :
    Option (CheckedDiscardedExpr source) :=
  match compileExprChecked? source with
  | some checked => some (CheckedDiscardedExpr.ofChecked checked)
  | none => none

def compileDiscardedExpr? (source : L03_GeneratedYul.Expr) :
    Option (List L04_StackCfg.Instr) :=
  match compileDiscardedExprChecked? source with
  | some checked => some checked.code
  | none => none

def compileNeutralStmtChecked? :
    (source : L03_GeneratedYul.Stmt) ->
      Option (CheckedNeutralStmt source)
  | L03_GeneratedYul.Stmt.skip =>
      some CheckedNeutralStmt.skip
  | L03_GeneratedYul.Stmt.expr expr =>
      match compileDiscardedExprChecked? expr with
      | some checked => some (CheckedNeutralStmt.expr checked)
      | none => none
  | _ => none

def compileNeutralStmt? (source : L03_GeneratedYul.Stmt) :
    Option (List L04_StackCfg.Instr) :=
  match compileNeutralStmtChecked? source with
  | some checked => some checked.code
  | none => none

theorem compileNeutralStmt?_addWords_eq
    (lhs rhs : L03_GeneratedYul.Word) :
    compileNeutralStmt?
        (L03_GeneratedYul.Stmt.expr
          (L03_GeneratedYul.Expr.add
            (L03_GeneratedYul.Expr.word lhs)
            (L03_GeneratedYul.Expr.word rhs))) =
      some
        [ L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
        , L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm rhs))
        , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add
        , L04_StackCfg.Instr.pop ] := by
  have hEval :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.add
          [L03_GeneratedYul.Expr.word lhs,
            L03_GeneratedYul.Expr.word rhs]).eval? =
        some
          (SharedSemantics.addWord
            (SharedSemantics.norm lhs) (SharedSemantics.norm rhs)) := by
    rfl
  simp [compileNeutralStmt?, compileNeutralStmtChecked?,
    compileDiscardedExprChecked?, CheckedDiscardedExpr.ofChecked,
    compileExprChecked?, L03_GeneratedYul.Expr.add,
    CheckedNeutralStmt.expr, CheckedExpr.add, CheckedExpr.word, hEval]

def compileNeutralStmtsChecked? :
    (source : List L03_GeneratedYul.Stmt) ->
      Option (CheckedNeutralStmts source)
  | [] => some CheckedNeutralStmts.nil
  | stmt :: rest =>
      match compileNeutralStmtChecked? stmt,
          compileNeutralStmtsChecked? rest with
      | some head, some tail =>
          some (CheckedNeutralStmts.cons head tail)
      | _, _ => none

def compileNeutralStmts? (source : List L03_GeneratedYul.Stmt) :
    Option (List L04_StackCfg.Instr) :=
  match compileNeutralStmtsChecked? source with
  | some checked => some checked.code
  | none => none

def compileNeutralBlockChecked? (source : List L03_GeneratedYul.Stmt) :
    Option (CheckedNeutralStmt (L03_GeneratedYul.Stmt.block source)) :=
  match compileNeutralStmtsChecked? source with
  | some checked => some (CheckedNeutralStmt.block checked)
  | none => none

def compileNeutralBlock? (source : List L03_GeneratedYul.Stmt) :
    Option (List L04_StackCfg.Instr) :=
  match compileNeutralBlockChecked? source with
  | some checked => some checked.code
  | none => none

def compileNeutralPrefixReturnExprArtifact?
    (prelude : List L03_GeneratedYul.Stmt)
    (source : L03_GeneratedYul.Expr) :
    Option Artifact :=
  match compileNeutralStmtsChecked? prelude,
      compileExprChecked? source with
  | some neutral, some checked =>
      some (Artifact.neutralThenReturnChecked neutral checked)
  | _, _ => none

def compileReturnStmtsChecked? :
    (source : List L03_GeneratedYul.Stmt) ->
      Option (CheckedReturnStmts source)
  | [] => none
  | [stmt] =>
      match hReturned : stmt.returnedExpr? with
      | none => none
      | some expr =>
          match compileExprChecked? expr with
          | some checked =>
              some (CheckedReturnStmts.returned hReturned checked)
          | none => none
  | stmt :: next :: rest =>
      match compileNeutralStmtChecked? stmt with
      | some head =>
          match compileReturnStmtsChecked? (next :: rest) with
          | some tail => some (CheckedReturnStmts.cons head tail)
          | none => none
      | none =>
          match stmt, next, rest with
          | L03_GeneratedYul.Stmt.expr
              (L03_GeneratedYul.Expr.builtin
                SolidCoreYulCore.Evm.Builtin.mstore
                [L03_GeneratedYul.Expr.word 0, storedExpr]),
            L03_GeneratedYul.Stmt.expr
              (L03_GeneratedYul.Expr.builtin
                SolidCoreYulCore.Evm.Builtin.returnOp
                [L03_GeneratedYul.Expr.word 0,
                  L03_GeneratedYul.Expr.word 32]),
            [] =>
              match compileExprChecked? storedExpr with
              | some checked =>
                  some
                    (CheckedReturnStmts.returnedBlock
                      (source :=
                        [ L03_GeneratedYul.Stmt.expr
                            (L03_GeneratedYul.Expr.builtin
                              SolidCoreYulCore.Evm.Builtin.mstore
                              [L03_GeneratedYul.Expr.word 0, storedExpr])
                        , L03_GeneratedYul.Stmt.expr
                            (L03_GeneratedYul.Expr.builtin
                              SolidCoreYulCore.Evm.Builtin.returnOp
                              [L03_GeneratedYul.Expr.word 0,
                                L03_GeneratedYul.Expr.word 32]) ])
                      (by
                        simp [L03_GeneratedYul.Stmt.returnedExpr?,
                          L03_GeneratedYul.Stmt.returnedExprs?])
                      checked)
              | none => none
          | _, _, _ => none

def compileReturnStmtsArtifact?
    (source : List L03_GeneratedYul.Stmt) : Option Artifact :=
  match compileReturnStmtsChecked? source with
  | some checked => some (Artifact.returnStmtsChecked checked)
  | none => none

def compileReturnBlockProgramArtifact?
    (source : List L03_GeneratedYul.Stmt) : Option Artifact :=
  compileReturnStmtsArtifact? source

def returnBlockStmts? (program : L03_GeneratedYul.Program) :
    Option (List L03_GeneratedYul.Stmt) :=
  match program.profile.layout, program.profile.abi, program.profile.events,
      program.profile.errors, program.profile.memoryRegions,
      program.profile.emittedHelpers, program.object.functions,
      program.object.data, program.object.subobjects, program.object.code with
  | [], [], [], [], [], [], [], [], [], L03_GeneratedYul.Stmt.block stmts =>
      some stmts
  | _, _, _, _, _, _, _, _, _, _ => none

theorem compileExpr?_sound
    {source : L03_GeneratedYul.Expr} {code : List L04_StackCfg.Instr}
    {value : L03_GeneratedYul.Word}
    (hCompile : compileExpr? source = some code)
    (hEval : source.Eval value)
    (stack : List L04_StackCfg.Word) :
    L04_StackCfg.execInstrs stack code = some (value :: stack) := by
  cases hChecked : compileExprChecked? source with
  | none =>
      simp [compileExpr?, hChecked] at hCompile
  | some checked =>
      simp [compileExpr?, hChecked] at hCompile
      cases hCompile
      have hValue : value = checked.value := by
        have hCheckedEval :
            source.eval? = some checked.value := by
          simpa [L03_GeneratedYul.Expr.Eval] using checked.eval
        have hSourceEval : source.eval? = some value := by
          simpa [L03_GeneratedYul.Expr.Eval] using hEval
        rw [hCheckedEval] at hSourceEval
        cases hSourceEval
        rfl
      cases hValue
      exact checked.exec stack

theorem compileExpr?_pseudoFree
    {source : L03_GeneratedYul.Expr} {code : List L04_StackCfg.Instr}
    (hCompile : compileExpr? source = some code) :
    L04_StackCfg.InstrsPseudoFree code := by
  cases hChecked : compileExprChecked? source with
  | none =>
      simp [compileExpr?, hChecked] at hCompile
  | some checked =>
      simp [compileExpr?, hChecked] at hCompile
      cases hCompile
      exact checked.pseudoFree

theorem compileExpr?_stackDepth
    {source : L03_GeneratedYul.Expr} {code : List L04_StackCfg.Instr}
    (hCompile : compileExpr? source = some code)
    (depth : Nat) :
    L04_StackCfg.stackDepthAfter? depth code = some (depth + 1) := by
  cases hChecked : compileExprChecked? source with
  | none =>
      simp [compileExpr?, hChecked] at hCompile
  | some checked =>
      simp [compileExpr?, hChecked] at hCompile
      cases hCompile
      exact checked.stackDepth depth

theorem compileDiscardedExpr?_pseudoFree
    {source : L03_GeneratedYul.Expr} {code : List L04_StackCfg.Instr}
    (hCompile : compileDiscardedExpr? source = some code) :
    L04_StackCfg.InstrsPseudoFree code := by
  cases hChecked : compileDiscardedExprChecked? source with
  | none =>
      simp [compileDiscardedExpr?, hChecked] at hCompile
  | some checked =>
      simp [compileDiscardedExpr?, hChecked] at hCompile
      cases hCompile
      exact checked.pseudoFree

theorem compileDiscardedExpr?_stackDepth
    {source : L03_GeneratedYul.Expr} {code : List L04_StackCfg.Instr}
    (hCompile : compileDiscardedExpr? source = some code)
    (depth : Nat) :
    L04_StackCfg.stackDepthAfter? depth code = some depth := by
  cases hChecked : compileDiscardedExprChecked? source with
  | none =>
      simp [compileDiscardedExpr?, hChecked] at hCompile
  | some checked =>
      simp [compileDiscardedExpr?, hChecked] at hCompile
      cases hCompile
      exact checked.stackDepth depth

theorem compileDiscardedExpr?_exec
    {source : L03_GeneratedYul.Expr} {code : List L04_StackCfg.Instr}
    (hCompile : compileDiscardedExpr? source = some code)
    (stack : List L04_StackCfg.Word) :
    L04_StackCfg.execInstrs stack code = some stack := by
  cases hChecked : compileDiscardedExprChecked? source with
  | none =>
      simp [compileDiscardedExpr?, hChecked] at hCompile
  | some checked =>
      simp [compileDiscardedExpr?, hChecked] at hCompile
      cases hCompile
      exact checked.exec stack

theorem compileNeutralStmt?_pseudoFree
    {source : L03_GeneratedYul.Stmt} {code : List L04_StackCfg.Instr}
    (hCompile : compileNeutralStmt? source = some code) :
    L04_StackCfg.InstrsPseudoFree code := by
  cases hChecked : compileNeutralStmtChecked? source with
  | none =>
      simp [compileNeutralStmt?, hChecked] at hCompile
  | some checked =>
      simp [compileNeutralStmt?, hChecked] at hCompile
      cases hCompile
      exact checked.pseudoFree

theorem compileNeutralStmt?_stackDepth
    {source : L03_GeneratedYul.Stmt} {code : List L04_StackCfg.Instr}
    (hCompile : compileNeutralStmt? source = some code)
    (depth : Nat) :
    L04_StackCfg.stackDepthAfter? depth code = some depth := by
  cases hChecked : compileNeutralStmtChecked? source with
  | none =>
      simp [compileNeutralStmt?, hChecked] at hCompile
  | some checked =>
      simp [compileNeutralStmt?, hChecked] at hCompile
      cases hCompile
      exact checked.stackDepth depth

theorem compileNeutralStmt?_exec
    {source : L03_GeneratedYul.Stmt} {code : List L04_StackCfg.Instr}
    (hCompile : compileNeutralStmt? source = some code)
    (stack : List L04_StackCfg.Word) :
    L04_StackCfg.execInstrs stack code = some stack := by
  cases hChecked : compileNeutralStmtChecked? source with
  | none =>
      simp [compileNeutralStmt?, hChecked] at hCompile
  | some checked =>
      simp [compileNeutralStmt?, hChecked] at hCompile
      cases hCompile
      exact checked.exec stack

theorem compileNeutralStmts?_pseudoFree
    {source : List L03_GeneratedYul.Stmt} {code : List L04_StackCfg.Instr}
    (hCompile : compileNeutralStmts? source = some code) :
    L04_StackCfg.InstrsPseudoFree code := by
  cases hChecked : compileNeutralStmtsChecked? source with
  | none =>
      simp [compileNeutralStmts?, hChecked] at hCompile
  | some checked =>
      simp [compileNeutralStmts?, hChecked] at hCompile
      cases hCompile
      exact checked.pseudoFree

theorem compileNeutralStmts?_stackDepth
    {source : List L03_GeneratedYul.Stmt} {code : List L04_StackCfg.Instr}
    (hCompile : compileNeutralStmts? source = some code)
    (depth : Nat) :
    L04_StackCfg.stackDepthAfter? depth code = some depth := by
  cases hChecked : compileNeutralStmtsChecked? source with
  | none =>
      simp [compileNeutralStmts?, hChecked] at hCompile
  | some checked =>
      simp [compileNeutralStmts?, hChecked] at hCompile
      cases hCompile
      exact checked.stackDepth depth

theorem compileNeutralStmts?_exec
    {source : List L03_GeneratedYul.Stmt} {code : List L04_StackCfg.Instr}
    (hCompile : compileNeutralStmts? source = some code)
    (stack : List L04_StackCfg.Word) :
    L04_StackCfg.execInstrs stack code = some stack := by
  cases hChecked : compileNeutralStmtsChecked? source with
  | none =>
      simp [compileNeutralStmts?, hChecked] at hCompile
  | some checked =>
      simp [compileNeutralStmts?, hChecked] at hCompile
      cases hCompile
      exact checked.exec stack

theorem compileNeutralBlock?_pseudoFree
    {source : List L03_GeneratedYul.Stmt} {code : List L04_StackCfg.Instr}
    (hCompile : compileNeutralBlock? source = some code) :
    L04_StackCfg.InstrsPseudoFree code := by
  cases hChecked : compileNeutralBlockChecked? source with
  | none =>
      simp [compileNeutralBlock?, hChecked] at hCompile
  | some checked =>
      simp [compileNeutralBlock?, hChecked] at hCompile
      cases hCompile
      exact checked.pseudoFree

theorem compileNeutralBlock?_stackDepth
    {source : List L03_GeneratedYul.Stmt} {code : List L04_StackCfg.Instr}
    (hCompile : compileNeutralBlock? source = some code)
    (depth : Nat) :
    L04_StackCfg.stackDepthAfter? depth code = some depth := by
  cases hChecked : compileNeutralBlockChecked? source with
  | none =>
      simp [compileNeutralBlock?, hChecked] at hCompile
  | some checked =>
      simp [compileNeutralBlock?, hChecked] at hCompile
      cases hCompile
      exact checked.stackDepth depth

theorem compileNeutralBlock?_exec
    {source : List L03_GeneratedYul.Stmt} {code : List L04_StackCfg.Instr}
    (hCompile : compileNeutralBlock? source = some code)
    (stack : List L04_StackCfg.Word) :
    L04_StackCfg.execInstrs stack code = some stack := by
  cases hChecked : compileNeutralBlockChecked? source with
  | none =>
      simp [compileNeutralBlock?, hChecked] at hCompile
  | some checked =>
      simp [compileNeutralBlock?, hChecked] at hCompile
      cases hCompile
      exact checked.exec stack

inductive AcceptedExpr :
    L03_GeneratedYul.Expr -> L03_GeneratedYul.Word -> Prop where
  | word (value : L03_GeneratedYul.Word) :
      AcceptedExpr (L03_GeneratedYul.Expr.word value)
        (SharedSemantics.norm value)
  | add {lhs rhs : L03_GeneratedYul.Expr}
      {lhsValue rhsValue : L03_GeneratedYul.Word} :
      AcceptedExpr lhs lhsValue ->
      AcceptedExpr rhs rhsValue ->
      (L03_GeneratedYul.Expr.add lhs rhs).Eval
        (SharedSemantics.addWord lhsValue rhsValue) ->
      AcceptedExpr (L03_GeneratedYul.Expr.add lhs rhs)
        (SharedSemantics.addWord lhsValue rhsValue)
  | mul {lhs rhs : L03_GeneratedYul.Expr}
      {lhsValue rhsValue : L03_GeneratedYul.Word} :
      AcceptedExpr lhs lhsValue ->
      AcceptedExpr rhs rhsValue ->
      (L03_GeneratedYul.Expr.mul lhs rhs).Eval
        (SharedSemantics.mulWord lhsValue rhsValue) ->
      AcceptedExpr (L03_GeneratedYul.Expr.mul lhs rhs)
        (SharedSemantics.mulWord lhsValue rhsValue)
  | sub {lhs rhs : L03_GeneratedYul.Expr}
      {lhsValue rhsValue : L03_GeneratedYul.Word} :
      AcceptedExpr lhs lhsValue ->
      AcceptedExpr rhs rhsValue ->
      (L03_GeneratedYul.Expr.sub lhs rhs).Eval
        (SharedSemantics.subWord lhsValue rhsValue) ->
      AcceptedExpr (L03_GeneratedYul.Expr.sub lhs rhs)
        (SharedSemantics.subWord lhsValue rhsValue)
  | iszero {source : L03_GeneratedYul.Expr}
      {value : L03_GeneratedYul.Word} :
      AcceptedExpr source value ->
      (L03_GeneratedYul.Expr.iszero source).Eval
        (SharedSemantics.iszeroWord value) ->
      AcceptedExpr (L03_GeneratedYul.Expr.iszero source)
        (SharedSemantics.iszeroWord value)
  | eqOp {lhs rhs : L03_GeneratedYul.Expr}
      {lhsValue rhsValue : L03_GeneratedYul.Word} :
      AcceptedExpr lhs lhsValue ->
      AcceptedExpr rhs rhsValue ->
      (L03_GeneratedYul.Expr.eqOp lhs rhs).Eval
        (SharedSemantics.eqWord lhsValue rhsValue) ->
      AcceptedExpr (L03_GeneratedYul.Expr.eqOp lhs rhs)
        (SharedSemantics.eqWord lhsValue rhsValue)

theorem AcceptedExpr.eval
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    source.Eval value := by
  cases hAccepted with
  | word value =>
      exact L03_GeneratedYul.Expr.word_eval_norm value
  | add _hLhsAccepted _hRhsAccepted hEval =>
      exact hEval
  | mul _hLhsAccepted _hRhsAccepted hEval =>
      exact hEval
  | sub _hLhsAccepted _hRhsAccepted hEval =>
      exact hEval
  | iszero _hAccepted hEval =>
      exact hEval
  | eqOp _hLhsAccepted _hRhsAccepted hEval =>
      exact hEval

inductive AcceptedNeutralStmt : L03_GeneratedYul.Stmt -> Prop where
  | skip :
      AcceptedNeutralStmt L03_GeneratedYul.Stmt.skip
  | expr {source : L03_GeneratedYul.Expr}
      {value : L03_GeneratedYul.Word} :
      AcceptedExpr source value ->
      AcceptedNeutralStmt (L03_GeneratedYul.Stmt.expr source)

inductive AcceptedNeutralStmts :
    List L03_GeneratedYul.Stmt -> Prop where
  | nil :
      AcceptedNeutralStmts []
  | cons {stmt : L03_GeneratedYul.Stmt}
      {rest : List L03_GeneratedYul.Stmt} :
      AcceptedNeutralStmt stmt ->
      AcceptedNeutralStmts rest ->
      AcceptedNeutralStmts (stmt :: rest)

inductive AcceptedReturnStmts :
    List L03_GeneratedYul.Stmt -> L03_GeneratedYul.Word -> Prop where
  | returned {stmt : L03_GeneratedYul.Stmt}
      {expr : L03_GeneratedYul.Expr}
      {value : L03_GeneratedYul.Word} :
      stmt.returnedExpr? = some expr ->
      AcceptedExpr expr value ->
      AcceptedReturnStmts [stmt] value
  | cons {stmt : L03_GeneratedYul.Stmt}
      {rest : List L03_GeneratedYul.Stmt}
      {value : L03_GeneratedYul.Word} :
      AcceptedNeutralStmt stmt ->
      AcceptedReturnStmts rest value ->
      AcceptedReturnStmts (stmt :: rest) value

def acceptExprChecked? :
    (source : L03_GeneratedYul.Expr) ->
      Option { value : L03_GeneratedYul.Word // AcceptedExpr source value }
  | L03_GeneratedYul.Expr.word value =>
      some ⟨SharedSemantics.norm value, AcceptedExpr.word value⟩
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.add [lhs, rhs] =>
      match acceptExprChecked? lhs, acceptExprChecked? rhs with
      | some lhsAccepted, some rhsAccepted =>
          let result :=
            SharedSemantics.addWord lhsAccepted.val rhsAccepted.val
          if hEval : (L03_GeneratedYul.Expr.add lhs rhs).eval? =
              some result then
            some
              ⟨result,
                by
                  simpa [L03_GeneratedYul.Expr.add] using
                    AcceptedExpr.add lhsAccepted.property
                      rhsAccepted.property
                      (by
                        simpa [L03_GeneratedYul.Expr.Eval] using
                          hEval)⟩
          else
            none
      | _, _ => none
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.mul [lhs, rhs] =>
      match acceptExprChecked? lhs, acceptExprChecked? rhs with
      | some lhsAccepted, some rhsAccepted =>
          let result :=
            SharedSemantics.mulWord lhsAccepted.val rhsAccepted.val
          if hEval : (L03_GeneratedYul.Expr.mul lhs rhs).eval? =
              some result then
            some
              ⟨result,
                by
                  simpa [L03_GeneratedYul.Expr.mul] using
                    AcceptedExpr.mul lhsAccepted.property
                      rhsAccepted.property
                      (by
                        simpa [L03_GeneratedYul.Expr.Eval] using
                          hEval)⟩
          else
            none
      | _, _ => none
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.sub [lhs, rhs] =>
      match acceptExprChecked? lhs, acceptExprChecked? rhs with
      | some lhsAccepted, some rhsAccepted =>
          let result :=
            SharedSemantics.subWord lhsAccepted.val rhsAccepted.val
          if hEval : (L03_GeneratedYul.Expr.sub lhs rhs).eval? =
              some result then
            some
              ⟨result,
                by
                  simpa [L03_GeneratedYul.Expr.sub] using
                    AcceptedExpr.sub lhsAccepted.property
                      rhsAccepted.property
                      (by
                        simpa [L03_GeneratedYul.Expr.Eval] using
                          hEval)⟩
          else
            none
      | _, _ => none
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.iszero [source] =>
      match acceptExprChecked? source with
      | some accepted =>
          let result := SharedSemantics.iszeroWord accepted.val
          if hEval : (L03_GeneratedYul.Expr.iszero source).eval? =
              some result then
            some
              ⟨result,
                by
                  simpa [L03_GeneratedYul.Expr.iszero] using
                    AcceptedExpr.iszero accepted.property
                      (by
                        simpa [L03_GeneratedYul.Expr.Eval] using
                          hEval)⟩
          else
            none
      | none => none
  | L03_GeneratedYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.eqOp [lhs, rhs] =>
      match acceptExprChecked? lhs, acceptExprChecked? rhs with
      | some lhsAccepted, some rhsAccepted =>
          let result :=
            SharedSemantics.eqWord lhsAccepted.val rhsAccepted.val
          if hEval : (L03_GeneratedYul.Expr.eqOp lhs rhs).eval? =
              some result then
            some
              ⟨result,
                by
                  simpa [L03_GeneratedYul.Expr.eqOp] using
                    AcceptedExpr.eqOp lhsAccepted.property
                      rhsAccepted.property
                      (by
                        simpa [L03_GeneratedYul.Expr.Eval] using
                          hEval)⟩
          else
            none
      | _, _ => none
  | _ => none

def acceptExpr? (source : L03_GeneratedYul.Expr) :
    Option L03_GeneratedYul.Word :=
  match acceptExprChecked? source with
  | some accepted => some accepted.val
  | none => none

def acceptNeutralStmt? : L03_GeneratedYul.Stmt -> Bool
  | L03_GeneratedYul.Stmt.skip => true
  | L03_GeneratedYul.Stmt.expr expr =>
      match acceptExpr? expr with
      | some _ => true
      | none => false
  | _ => false

def acceptNeutralStmts? : List L03_GeneratedYul.Stmt -> Bool
  | [] => true
  | stmt :: rest =>
      acceptNeutralStmt? stmt && acceptNeutralStmts? rest

def acceptReturnStmts? :
    List L03_GeneratedYul.Stmt -> Option L03_GeneratedYul.Word
  | [] => none
  | [stmt] =>
      match stmt.returnedExpr? with
      | some expr => acceptExpr? expr
      | none => none
  | stmt :: next :: rest =>
      if acceptNeutralStmt? stmt then
        acceptReturnStmts? (next :: rest)
      else
        none

theorem acceptExpr?_sound
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccept : acceptExpr? source = some value) :
    AcceptedExpr source value := by
  cases hChecked : acceptExprChecked? source with
  | none =>
      simp [acceptExpr?, hChecked] at hAccept
  | some accepted =>
      simp [acceptExpr?, hChecked] at hAccept
      cases hAccept
      exact accepted.property

theorem acceptExprChecked?_complete
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    ∃ accepted : { value : L03_GeneratedYul.Word //
        AcceptedExpr source value },
      acceptExprChecked? source = some accepted ∧
        accepted.val = value := by
  induction hAccepted with
  | word value =>
      exact
        ⟨⟨SharedSemantics.norm value, AcceptedExpr.word value⟩, rfl, rfl⟩
  | add hLhsAccepted hRhsAccepted hEval ihLhs ihRhs =>
      rename_i lhs rhs lhsValue rhsValue
      rcases ihLhs with ⟨lhsAccepted, hLhs, hLhsValue⟩
      rcases ihRhs with ⟨rhsAccepted, hRhs, hRhsValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.add lhs rhs).Eval
            (SharedSemantics.addWord lhsAccepted.val
              rhsAccepted.val) := by
        cases hLhsValue
        cases hRhsValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.add lhs rhs).eval? =
            some
              (SharedSemantics.addWord lhsAccepted.val
                rhsAccepted.val) := by
        simpa [L03_GeneratedYul.Expr.Eval] using hEvalChecked
      refine
        ⟨⟨SharedSemantics.addWord lhsAccepted.val rhsAccepted.val,
            by
              simpa [L03_GeneratedYul.Expr.add] using
                AcceptedExpr.add lhsAccepted.property
                  rhsAccepted.property hEvalChecked⟩, ?_, ?_⟩
      · simp [acceptExprChecked?, L03_GeneratedYul.Expr.add, hLhs, hRhs]
        simpa [L03_GeneratedYul.Expr.add] using hEvalEq
      · cases hLhsValue
        cases hRhsValue
        rfl
  | mul hLhsAccepted hRhsAccepted hEval ihLhs ihRhs =>
      rename_i lhs rhs lhsValue rhsValue
      rcases ihLhs with ⟨lhsAccepted, hLhs, hLhsValue⟩
      rcases ihRhs with ⟨rhsAccepted, hRhs, hRhsValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.mul lhs rhs).Eval
            (SharedSemantics.mulWord lhsAccepted.val
              rhsAccepted.val) := by
        cases hLhsValue
        cases hRhsValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.mul lhs rhs).eval? =
            some
              (SharedSemantics.mulWord lhsAccepted.val
                rhsAccepted.val) := by
        simpa [L03_GeneratedYul.Expr.Eval] using hEvalChecked
      refine
        ⟨⟨SharedSemantics.mulWord lhsAccepted.val rhsAccepted.val,
            by
              simpa [L03_GeneratedYul.Expr.mul] using
                AcceptedExpr.mul lhsAccepted.property
                  rhsAccepted.property hEvalChecked⟩, ?_, ?_⟩
      · simp [acceptExprChecked?, L03_GeneratedYul.Expr.mul, hLhs, hRhs]
        simpa [L03_GeneratedYul.Expr.mul] using hEvalEq
      · cases hLhsValue
        cases hRhsValue
        rfl
  | sub hLhsAccepted hRhsAccepted hEval ihLhs ihRhs =>
      rename_i lhs rhs lhsValue rhsValue
      rcases ihLhs with ⟨lhsAccepted, hLhs, hLhsValue⟩
      rcases ihRhs with ⟨rhsAccepted, hRhs, hRhsValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.sub lhs rhs).Eval
            (SharedSemantics.subWord lhsAccepted.val
              rhsAccepted.val) := by
        cases hLhsValue
        cases hRhsValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.sub lhs rhs).eval? =
            some
              (SharedSemantics.subWord lhsAccepted.val
                rhsAccepted.val) := by
        simpa [L03_GeneratedYul.Expr.Eval] using hEvalChecked
      refine
        ⟨⟨SharedSemantics.subWord lhsAccepted.val rhsAccepted.val,
            by
              simpa [L03_GeneratedYul.Expr.sub] using
                AcceptedExpr.sub lhsAccepted.property
                  rhsAccepted.property hEvalChecked⟩, ?_, ?_⟩
      · simp [acceptExprChecked?, L03_GeneratedYul.Expr.sub, hLhs, hRhs]
        simpa [L03_GeneratedYul.Expr.sub] using hEvalEq
      · cases hLhsValue
        cases hRhsValue
        rfl
  | iszero hAccepted hEval ih =>
      rename_i source value
      rcases ih with ⟨accepted, hAcceptedChecked, hAcceptedValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.iszero source).Eval
            (SharedSemantics.iszeroWord accepted.val) := by
        cases hAcceptedValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.iszero source).eval? =
            some (SharedSemantics.iszeroWord accepted.val) := by
        simpa [L03_GeneratedYul.Expr.Eval] using hEvalChecked
      refine
        ⟨⟨SharedSemantics.iszeroWord accepted.val,
            by
              simpa [L03_GeneratedYul.Expr.iszero] using
                AcceptedExpr.iszero accepted.property hEvalChecked⟩, ?_, ?_⟩
      · simp [acceptExprChecked?, L03_GeneratedYul.Expr.iszero,
          hAcceptedChecked]
        simpa [L03_GeneratedYul.Expr.iszero] using hEvalEq
      · cases hAcceptedValue
        rfl
  | eqOp hLhsAccepted hRhsAccepted hEval ihLhs ihRhs =>
      rename_i lhs rhs lhsValue rhsValue
      rcases ihLhs with ⟨lhsAccepted, hLhs, hLhsValue⟩
      rcases ihRhs with ⟨rhsAccepted, hRhs, hRhsValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.eqOp lhs rhs).Eval
            (SharedSemantics.eqWord lhsAccepted.val
              rhsAccepted.val) := by
        cases hLhsValue
        cases hRhsValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.eqOp lhs rhs).eval? =
            some
              (SharedSemantics.eqWord lhsAccepted.val
                rhsAccepted.val) := by
        simpa [L03_GeneratedYul.Expr.Eval] using hEvalChecked
      refine
        ⟨⟨SharedSemantics.eqWord lhsAccepted.val rhsAccepted.val,
            by
              simpa [L03_GeneratedYul.Expr.eqOp] using
                AcceptedExpr.eqOp lhsAccepted.property
                  rhsAccepted.property hEvalChecked⟩, ?_, ?_⟩
      · simp [acceptExprChecked?, L03_GeneratedYul.Expr.eqOp, hLhs, hRhs]
        simpa [L03_GeneratedYul.Expr.eqOp] using hEvalEq
      · cases hLhsValue
        cases hRhsValue
        rfl

theorem acceptExpr?_complete
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    acceptExpr? source = some value := by
  rcases acceptExprChecked?_complete hAccepted with
    ⟨accepted, hChecked, hValue⟩
  cases hValue
  simp [acceptExpr?, hChecked]

theorem acceptNeutralStmt?_sound
    {source : L03_GeneratedYul.Stmt}
    (hAccept : acceptNeutralStmt? source = true) :
    AcceptedNeutralStmt source := by
  cases source <;> simp [acceptNeutralStmt?] at hAccept ⊢
  · exact AcceptedNeutralStmt.skip
  · rename_i expr
    cases hExpr : acceptExpr? expr with
    | none =>
        simp [hExpr] at hAccept
    | some value =>
        exact AcceptedNeutralStmt.expr (acceptExpr?_sound hExpr)

theorem acceptNeutralStmt?_complete
    {source : L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmt source) :
    acceptNeutralStmt? source = true := by
  cases hAccepted with
  | skip =>
      rfl
  | expr hExprAccepted =>
      have hExpr := acceptExpr?_complete hExprAccepted
      simp [acceptNeutralStmt?, hExpr]

theorem acceptNeutralStmts?_sound
    {source : List L03_GeneratedYul.Stmt}
    (hAccept : acceptNeutralStmts? source = true) :
    AcceptedNeutralStmts source := by
  induction source with
  | nil =>
      exact AcceptedNeutralStmts.nil
  | cons stmt rest ih =>
      simp [acceptNeutralStmts?] at hAccept
      exact AcceptedNeutralStmts.cons
        (acceptNeutralStmt?_sound hAccept.left)
        (ih hAccept.right)

theorem acceptNeutralStmts?_complete
    {source : List L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmts source) :
    acceptNeutralStmts? source = true := by
  induction hAccepted with
  | nil =>
      rfl
  | cons hStmt hRest ih =>
      simp [acceptNeutralStmts?, acceptNeutralStmt?_complete hStmt, ih]

theorem acceptReturnStmts?_sound
    {source : List L03_GeneratedYul.Stmt}
    {value : L03_GeneratedYul.Word}
    (hAccept : acceptReturnStmts? source = some value) :
    AcceptedReturnStmts source value := by
  induction source with
  | nil =>
      simp [acceptReturnStmts?] at hAccept
  | cons stmt rest ih =>
      cases rest with
      | nil =>
          simp [acceptReturnStmts?] at hAccept
          cases hReturned : stmt.returnedExpr? with
          | none =>
              simp [hReturned] at hAccept
          | some expr =>
              simp [hReturned] at hAccept
              exact AcceptedReturnStmts.returned hReturned
                (acceptExpr?_sound hAccept)
      | cons next rest' =>
          simp [acceptReturnStmts?] at hAccept
          cases hNeutral : acceptNeutralStmt? stmt <;>
            simp [hNeutral] at hAccept
          exact AcceptedReturnStmts.cons
            (acceptNeutralStmt?_sound hNeutral) (ih hAccept)

theorem acceptReturnStmts?_complete
    {source : List L03_GeneratedYul.Stmt}
    {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedReturnStmts source value) :
    acceptReturnStmts? source = some value := by
  induction hAccepted with
  | returned hReturned hExprAccepted =>
      simp [acceptReturnStmts?, hReturned,
        acceptExpr?_complete hExprAccepted]
  | cons hStmt hRest ih =>
      rename_i stmt rest value
      cases rest with
      | nil =>
          cases hRest
      | cons next rest' =>
          simp [acceptReturnStmts?,
            acceptNeutralStmt?_complete hStmt, ih]

theorem compileExprChecked?_complete_for_accepted
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    ∃ checked : CheckedExpr source,
      compileExprChecked? source = some checked ∧
        checked.value = value := by
  induction hAccepted with
  | word value =>
      exact ⟨CheckedExpr.word value, rfl, rfl⟩
  | add hLhsAccepted hRhsAccepted hEval ihLhs ihRhs =>
      rename_i lhs rhs lhsValue rhsValue
      rcases ihLhs with ⟨lhsChecked, hLhs, hLhsValue⟩
      rcases ihRhs with ⟨rhsChecked, hRhs, hRhsValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.add lhs rhs).Eval
            (SharedSemantics.addWord lhsChecked.value
              rhsChecked.value) := by
        cases hLhsValue
        cases hRhsValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.add [lhs, rhs]).eval? =
            some
              (SharedSemantics.addWord lhsChecked.value
                rhsChecked.value) := by
        simpa [L03_GeneratedYul.Expr.Eval,
          L03_GeneratedYul.Expr.add] using hEvalChecked
      refine
        ⟨CheckedExpr.add lhsChecked rhsChecked hEvalChecked, ?_, ?_⟩
      · simp [compileExprChecked?, L03_GeneratedYul.Expr.add,
          hLhs, hRhs, hEvalEq]
      · cases hLhsValue
        cases hRhsValue
        rfl
  | mul hLhsAccepted hRhsAccepted hEval ihLhs ihRhs =>
      rename_i lhs rhs lhsValue rhsValue
      rcases ihLhs with ⟨lhsChecked, hLhs, hLhsValue⟩
      rcases ihRhs with ⟨rhsChecked, hRhs, hRhsValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.mul lhs rhs).Eval
            (SharedSemantics.mulWord lhsChecked.value
              rhsChecked.value) := by
        cases hLhsValue
        cases hRhsValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.mul [lhs, rhs]).eval? =
            some
              (SharedSemantics.mulWord lhsChecked.value
                rhsChecked.value) := by
        simpa [L03_GeneratedYul.Expr.Eval,
          L03_GeneratedYul.Expr.mul] using hEvalChecked
      refine
        ⟨CheckedExpr.mul lhsChecked rhsChecked hEvalChecked, ?_, ?_⟩
      · simp [compileExprChecked?, L03_GeneratedYul.Expr.mul,
          hLhs, hRhs, hEvalEq]
      · cases hLhsValue
        cases hRhsValue
        rfl
  | sub hLhsAccepted hRhsAccepted hEval ihLhs ihRhs =>
      rename_i lhs rhs lhsValue rhsValue
      rcases ihLhs with ⟨lhsChecked, hLhs, hLhsValue⟩
      rcases ihRhs with ⟨rhsChecked, hRhs, hRhsValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.sub lhs rhs).Eval
            (SharedSemantics.subWord lhsChecked.value
              rhsChecked.value) := by
        cases hLhsValue
        cases hRhsValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.sub [lhs, rhs]).eval? =
            some
              (SharedSemantics.subWord lhsChecked.value
                rhsChecked.value) := by
        simpa [L03_GeneratedYul.Expr.Eval,
          L03_GeneratedYul.Expr.sub] using hEvalChecked
      refine
        ⟨CheckedExpr.sub lhsChecked rhsChecked hEvalChecked, ?_, ?_⟩
      · simp [compileExprChecked?, L03_GeneratedYul.Expr.sub,
          hLhs, hRhs, hEvalEq]
      · cases hLhsValue
        cases hRhsValue
        rfl
  | iszero hAccepted hEval ih =>
      rename_i source value
      rcases ih with ⟨checked, hChecked, hCheckedValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.iszero source).Eval
            (SharedSemantics.iszeroWord checked.value) := by
        cases hCheckedValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.iszero [source]).eval? =
            some (SharedSemantics.iszeroWord checked.value) := by
        simpa [L03_GeneratedYul.Expr.Eval,
          L03_GeneratedYul.Expr.iszero] using hEvalChecked
      refine
        ⟨CheckedExpr.iszero checked hEvalChecked, ?_, ?_⟩
      · simp [compileExprChecked?, L03_GeneratedYul.Expr.iszero,
          hChecked, hEvalEq]
      · cases hCheckedValue
        rfl
  | eqOp hLhsAccepted hRhsAccepted hEval ihLhs ihRhs =>
      rename_i lhs rhs lhsValue rhsValue
      rcases ihLhs with ⟨lhsChecked, hLhs, hLhsValue⟩
      rcases ihRhs with ⟨rhsChecked, hRhs, hRhsValue⟩
      have hEvalChecked :
          (L03_GeneratedYul.Expr.eqOp lhs rhs).Eval
            (SharedSemantics.eqWord lhsChecked.value
              rhsChecked.value) := by
        cases hLhsValue
        cases hRhsValue
        exact hEval
      have hEvalEq :
          (L03_GeneratedYul.Expr.builtin
            SolidCoreYulCore.Evm.Builtin.eqOp [lhs, rhs]).eval? =
            some
              (SharedSemantics.eqWord lhsChecked.value
                rhsChecked.value) := by
        simpa [L03_GeneratedYul.Expr.Eval,
          L03_GeneratedYul.Expr.eqOp] using hEvalChecked
      refine
        ⟨CheckedExpr.eqOp lhsChecked rhsChecked hEvalChecked, ?_, ?_⟩
      · simp [compileExprChecked?, L03_GeneratedYul.Expr.eqOp,
          hLhs, hRhs, hEvalEq]
      · cases hLhsValue
        cases hRhsValue
        rfl

theorem compileExpr?_complete_for_accepted
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    ∃ code, compileExpr? source = some code := by
  rcases compileExprChecked?_complete_for_accepted hAccepted with
    ⟨checked, hChecked, _hValue⟩
  exact ⟨checked.code, by simp [compileExpr?, hChecked]⟩

theorem compileExprChecked?_jumpReturnArtifact_sound_for_accepted
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    ∃ checked : CheckedExpr source,
      compileExprChecked? source = some checked ∧
        checked.value = value ∧
          L04_StackCfg.Reaches (Artifact.jumpReturnChecked checked).program
            (L04_StackCfg.Config.at
              (Artifact.jumpReturnChecked checked).program.entry [])
            (L04_StackCfg.Config.returnedWord value) := by
  rcases compileExprChecked?_complete_for_accepted hAccepted with
    ⟨checked, hChecked, hValue⟩
  refine ⟨checked, hChecked, hValue, ?_⟩
  cases hValue
  exact Artifact.jumpReturnChecked_reaches checked

theorem compileDiscardedExprChecked?_complete_for_accepted
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    ∃ checked : CheckedDiscardedExpr source,
      compileDiscardedExprChecked? source = some checked ∧
        checked.value = value := by
  rcases compileExprChecked?_complete_for_accepted hAccepted with
    ⟨checked, hChecked, hValue⟩
  exact
    ⟨CheckedDiscardedExpr.ofChecked checked,
      by simp [compileDiscardedExprChecked?, hChecked],
      hValue⟩

theorem compileDiscardedExpr?_complete_for_accepted
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    ∃ code, compileDiscardedExpr? source = some code := by
  rcases compileDiscardedExprChecked?_complete_for_accepted hAccepted with
    ⟨checked, hChecked, _hValue⟩
  exact ⟨checked.code, by simp [compileDiscardedExpr?, hChecked]⟩

theorem compileNeutralStmtChecked?_complete_for_accepted
    {source : L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmt source) :
    ∃ checked : CheckedNeutralStmt source,
      compileNeutralStmtChecked? source = some checked := by
  cases hAccepted with
  | skip =>
      exact ⟨CheckedNeutralStmt.skip, rfl⟩
  | expr hExprAccepted =>
      rcases compileDiscardedExprChecked?_complete_for_accepted
          hExprAccepted with
        ⟨checked, hChecked, _hValue⟩
      exact
        ⟨CheckedNeutralStmt.expr checked,
          by simp [compileNeutralStmtChecked?, hChecked]⟩

theorem compileNeutralStmt?_complete_for_accepted
    {source : L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmt source) :
    ∃ code, compileNeutralStmt? source = some code := by
  rcases compileNeutralStmtChecked?_complete_for_accepted hAccepted with
    ⟨checked, hChecked⟩
  exact ⟨checked.code, by simp [compileNeutralStmt?, hChecked]⟩

theorem compileNeutralStmtsChecked?_complete_for_accepted
    {source : List L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmts source) :
    ∃ checked : CheckedNeutralStmts source,
      compileNeutralStmtsChecked? source = some checked := by
  induction hAccepted with
  | nil =>
      exact ⟨CheckedNeutralStmts.nil, rfl⟩
  | cons hStmt hRest ih =>
      rcases compileNeutralStmtChecked?_complete_for_accepted
          hStmt with
        ⟨head, hHead⟩
      rcases ih with ⟨tail, hTail⟩
      exact
        ⟨CheckedNeutralStmts.cons head tail,
          by simp [compileNeutralStmtsChecked?, hHead, hTail]⟩

theorem compileNeutralStmts?_complete_for_accepted
    {source : List L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmts source) :
    ∃ code, compileNeutralStmts? source = some code := by
  rcases compileNeutralStmtsChecked?_complete_for_accepted hAccepted with
    ⟨checked, hChecked⟩
  exact ⟨checked.code, by simp [compileNeutralStmts?, hChecked]⟩

theorem compileNeutralBlockChecked?_complete_for_accepted
    {source : List L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmts source) :
    ∃ checked : CheckedNeutralStmt (L03_GeneratedYul.Stmt.block source),
      compileNeutralBlockChecked? source = some checked := by
  rcases compileNeutralStmtsChecked?_complete_for_accepted hAccepted with
    ⟨checked, hChecked⟩
  exact
    ⟨CheckedNeutralStmt.block checked,
      by simp [compileNeutralBlockChecked?, hChecked]⟩

theorem compileNeutralBlock?_complete_for_accepted
    {source : List L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmts source) :
    ∃ code, compileNeutralBlock? source = some code := by
  rcases compileNeutralBlockChecked?_complete_for_accepted hAccepted with
    ⟨checked, hChecked⟩
  exact ⟨checked.code, by simp [compileNeutralBlock?, hChecked]⟩

theorem compileNeutralPrefixReturnExprArtifact?_complete_for_accepted
    {prelude : List L03_GeneratedYul.Stmt}
    {source : L03_GeneratedYul.Expr}
    {value : L03_GeneratedYul.Word}
    (hPrefix : AcceptedNeutralStmts prelude)
    (hAccepted : AcceptedExpr source value) :
    ∃ artifact,
      compileNeutralPrefixReturnExprArtifact? prelude source =
        some artifact ∧
        L04_StackCfg.WF artifact.program ∧
        L04_StackCfg.Semantics artifact.program
          (L01_ValidSolidity.Behavior.returnedWord value) := by
  rcases compileNeutralStmtsChecked?_complete_for_accepted hPrefix with
    ⟨neutral, hNeutral⟩
  rcases compileExprChecked?_complete_for_accepted hAccepted with
    ⟨checked, hChecked, hValue⟩
  refine
    ⟨Artifact.neutralThenReturnChecked neutral checked, ?_, ?_, ?_⟩
  · simp [compileNeutralPrefixReturnExprArtifact?, hNeutral, hChecked]
  · exact (Artifact.neutralThenReturnChecked neutral checked).wf
  · cases hValue
    exact Artifact.neutralThenReturnChecked_semantics neutral checked

theorem compileReturnStmtsChecked?_complete_for_accepted
    {source : List L03_GeneratedYul.Stmt}
    {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedReturnStmts source value) :
    ∃ checked : CheckedReturnStmts source,
      compileReturnStmtsChecked? source = some checked ∧
        checked.value = value := by
  induction hAccepted with
  | returned hReturned hExprAccepted =>
      unfold compileReturnStmtsChecked?
      split
      · rename_i hNone
        rw [hNone] at hReturned
        cases hReturned
      · rename_i returnedExpr hReturnedActual
        rw [hReturnedActual] at hReturned
        cases hReturned
        rcases compileExprChecked?_complete_for_accepted
            hExprAccepted with
          ⟨checked, hChecked, hValue⟩
        split
        · rename_i hCheckedActual
          rw [hCheckedActual] at hChecked
          cases hChecked
          exact
            ⟨CheckedReturnStmts.returned hReturnedActual checked,
              rfl, hValue⟩
        · rename_i hNone
          rw [hNone] at hChecked
          cases hChecked
  | cons hStmt hRest ih =>
      rename_i stmt rest value
      cases rest with
      | nil =>
          cases hRest
      | cons next rest' =>
          rcases compileNeutralStmtChecked?_complete_for_accepted
              hStmt with
            ⟨head, hHead⟩
          rcases ih with ⟨tail, hTail, hValue⟩
          exact
            ⟨CheckedReturnStmts.cons head tail,
              by simp [compileReturnStmtsChecked?, hHead, hTail],
              hValue⟩

theorem compileReturnStmtsArtifact?_complete_for_accepted
    {source : List L03_GeneratedYul.Stmt}
    {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedReturnStmts source value) :
    ∃ artifact,
      compileReturnStmtsArtifact? source = some artifact ∧
        L04_StackCfg.WF artifact.program ∧
        L04_StackCfg.Semantics artifact.program
          (L01_ValidSolidity.Behavior.returnedWord value) := by
  rcases compileReturnStmtsChecked?_complete_for_accepted
      hAccepted with
    ⟨checked, hChecked, hValue⟩
  refine ⟨Artifact.returnStmtsChecked checked, ?_, ?_, ?_⟩
  · simp [compileReturnStmtsArtifact?, hChecked]
  · exact (Artifact.returnStmtsChecked checked).wf
  · cases hValue
    exact Artifact.returnStmtsChecked_semantics checked

theorem compileReturnStmtsArtifact?_sound_for_acceptReturnStmts?
    {source : List L03_GeneratedYul.Stmt}
    {value : L03_GeneratedYul.Word}
    (hAccept : acceptReturnStmts? source = some value) :
    ∃ artifact,
      compileReturnStmtsArtifact? source = some artifact ∧
        L04_StackCfg.WF artifact.program ∧
        L04_StackCfg.Semantics artifact.program
          (L01_ValidSolidity.Behavior.returnedWord value) := by
  exact compileReturnStmtsArtifact?_complete_for_accepted
    (acceptReturnStmts?_sound hAccept)

theorem compileReturnBlockProgramArtifact?_sound_for_acceptReturnStmts?
    {source : List L03_GeneratedYul.Stmt}
    {value : L03_GeneratedYul.Word}
    (hAccept : acceptReturnStmts? source = some value) :
    ∃ artifact,
      compileReturnBlockProgramArtifact? source = some artifact ∧
        L03_GeneratedYul.WF
          (L03_GeneratedYul.Program.returnStmt
            (L03_GeneratedYul.Stmt.block source)) ∧
        L04_StackCfg.WF artifact.program ∧
        L04_StackCfg.Semantics artifact.program
          (L01_ValidSolidity.Behavior.returnedWord value) := by
  rcases compileReturnStmtsArtifact?_sound_for_acceptReturnStmts?
      hAccept with
    ⟨artifact, hCompile, hWF, hSemantics⟩
  exact
    ⟨artifact,
      by simpa [compileReturnBlockProgramArtifact?] using hCompile,
      L03_GeneratedYul.Program.returnStmt_wf
        (L03_GeneratedYul.Stmt.block source),
      hWF,
      hSemantics⟩

theorem returnBlockStmts?_eq_returnStmt
    {program : L03_GeneratedYul.Program}
    {stmts : List L03_GeneratedYul.Stmt}
    (hBlock : returnBlockStmts? program = some stmts) :
    program =
      L03_GeneratedYul.Program.returnStmt
        (L03_GeneratedYul.Stmt.block stmts) := by
  cases program with
  | mk object profile =>
      cases object with
      | mk code functions data subobjects =>
          cases profile with
          | mk layout abi events errors memoryRegions emittedHelpers =>
              cases layout <;> cases abi <;> cases events <;>
                cases errors <;> cases memoryRegions <;>
                cases emittedHelpers <;> cases functions <;>
                cases data <;> cases subobjects <;> cases code <;>
                simp [returnBlockStmts?, L03_GeneratedYul.Program.returnStmt,
                  L03_GeneratedYul.Object.returnStmt,
                  L03_GeneratedYul.Profile.empty] at hBlock ⊢
              exact hBlock

theorem wf_of_returnBlockStmts?
    {program : L03_GeneratedYul.Program}
    {stmts : List L03_GeneratedYul.Stmt}
    (hBlock : returnBlockStmts? program = some stmts) :
    L03_GeneratedYul.WF program := by
  rw [returnBlockStmts?_eq_returnStmt hBlock]
  exact L03_GeneratedYul.Program.returnStmt_wf
    (L03_GeneratedYul.Stmt.block stmts)

theorem compileExpr?_sound_for_accepted
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    ∃ code,
      compileExpr? source = some code ∧
        L04_StackCfg.InstrsPseudoFree code ∧
        (∀ depth : Nat,
          L04_StackCfg.stackDepthAfter? depth code = some (depth + 1)) ∧
        (∀ stack : List L04_StackCfg.Word,
          L04_StackCfg.execInstrs stack code = some (value :: stack)) := by
  rcases compileExpr?_complete_for_accepted hAccepted with
    ⟨code, hCompile⟩
  exact
    ⟨code, hCompile,
      compileExpr?_pseudoFree hCompile,
      compileExpr?_stackDepth hCompile,
      fun stack =>
        compileExpr?_sound hCompile (AcceptedExpr.eval hAccepted) stack⟩

theorem compileDiscardedExpr?_sound_for_accepted
    {source : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word}
    (hAccepted : AcceptedExpr source value) :
    ∃ code,
      compileDiscardedExpr? source = some code ∧
        L04_StackCfg.InstrsPseudoFree code ∧
        (∀ depth : Nat,
          L04_StackCfg.stackDepthAfter? depth code = some depth) ∧
        (∀ stack : List L04_StackCfg.Word,
          L04_StackCfg.execInstrs stack code = some stack) := by
  rcases compileDiscardedExpr?_complete_for_accepted hAccepted with
    ⟨code, hCompile⟩
  exact
    ⟨code, hCompile,
      compileDiscardedExpr?_pseudoFree hCompile,
      compileDiscardedExpr?_stackDepth hCompile,
      compileDiscardedExpr?_exec hCompile⟩

theorem compileNeutralStmt?_sound_for_accepted
    {source : L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmt source) :
    ∃ code,
      compileNeutralStmt? source = some code ∧
        L04_StackCfg.InstrsPseudoFree code ∧
        (∀ depth : Nat,
          L04_StackCfg.stackDepthAfter? depth code = some depth) ∧
        (∀ stack : List L04_StackCfg.Word,
          L04_StackCfg.execInstrs stack code = some stack) := by
  rcases compileNeutralStmt?_complete_for_accepted hAccepted with
    ⟨code, hCompile⟩
  exact
    ⟨code, hCompile,
      compileNeutralStmt?_pseudoFree hCompile,
      compileNeutralStmt?_stackDepth hCompile,
      compileNeutralStmt?_exec hCompile⟩

theorem compileNeutralStmts?_sound_for_accepted
    {source : List L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmts source) :
    ∃ code,
      compileNeutralStmts? source = some code ∧
        L04_StackCfg.InstrsPseudoFree code ∧
        (∀ depth : Nat,
          L04_StackCfg.stackDepthAfter? depth code = some depth) ∧
        (∀ stack : List L04_StackCfg.Word,
          L04_StackCfg.execInstrs stack code = some stack) := by
  rcases compileNeutralStmts?_complete_for_accepted hAccepted with
    ⟨code, hCompile⟩
  exact
    ⟨code, hCompile,
      compileNeutralStmts?_pseudoFree hCompile,
      compileNeutralStmts?_stackDepth hCompile,
      compileNeutralStmts?_exec hCompile⟩

theorem compileNeutralBlock?_sound_for_accepted
    {source : List L03_GeneratedYul.Stmt}
    (hAccepted : AcceptedNeutralStmts source) :
    ∃ code,
      compileNeutralBlock? source = some code ∧
        L04_StackCfg.InstrsPseudoFree code ∧
        (∀ depth : Nat,
          L04_StackCfg.stackDepthAfter? depth code = some depth) ∧
        (∀ stack : List L04_StackCfg.Word,
          L04_StackCfg.execInstrs stack code = some stack) := by
  rcases compileNeutralBlock?_complete_for_accepted hAccepted with
    ⟨code, hCompile⟩
  exact
    ⟨code, hCompile,
      compileNeutralBlock?_pseudoFree hCompile,
      compileNeutralBlock?_stackDepth hCompile,
      compileNeutralBlock?_exec hCompile⟩

theorem compileExpr?_add1And2_eq :
    compileExpr? L03_GeneratedYul.Expr.add1And2 =
      some
        [ L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 1)
        , L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 2)
        , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ] := by
  have hEval :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.add
          [L03_GeneratedYul.Expr.word 1,
            L03_GeneratedYul.Expr.word 2]).eval? =
        some
          (SharedSemantics.addWord
            (SharedSemantics.norm 1) (SharedSemantics.norm 2)) := by
    rfl
  simp [compileExpr?, compileExprChecked?, CheckedExpr.add,
    CheckedExpr.word, L03_GeneratedYul.Expr.add1And2,
    L03_GeneratedYul.Expr.add, L03_GeneratedYul.Expr.word1,
    L03_GeneratedYul.Expr.word2, hEval, SharedSemantics.addWord,
    SharedSemantics.norm, SharedSemantics.norm,
    SharedSemantics.wordModulus]

theorem compileExpr?_add1And2_sound
    (stack : List L04_StackCfg.Word) :
    L04_StackCfg.execInstrs stack
        [ L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 1)
        , L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 2)
        , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ] =
      some (3 :: stack) := by
  simpa [compileExpr?_add1And2_eq] using
    compileExpr?_sound compileExpr?_add1And2_eq (by rfl) stack

theorem compileExpr?_word_eq (value : L03_GeneratedYul.Word) :
    compileExpr? (L03_GeneratedYul.Expr.word value) =
      some
        [L04_StackCfg.Instr.push
          (L04_StackCfg.Atom.word (SharedSemantics.norm value))] := by
  rfl

theorem compileExpr?_word_sound
    (value : L03_GeneratedYul.Word)
    (stack : List L04_StackCfg.Word) :
    L04_StackCfg.execInstrs stack
        [L04_StackCfg.Instr.push
          (L04_StackCfg.Atom.word (SharedSemantics.norm value))] =
      some (SharedSemantics.norm value :: stack) := by
  simpa [compileExpr?_word_eq] using
    compileExpr?_sound (compileExpr?_word_eq value)
      (L03_GeneratedYul.Expr.word_eval_norm value) stack

theorem compileExpr?_addChecked_eq
    {lhs rhs : L03_GeneratedYul.Expr}
    {lhsChecked : CheckedExpr lhs} {rhsChecked : CheckedExpr rhs}
    (hLhs : compileExprChecked? lhs = some lhsChecked)
    (hRhs : compileExprChecked? rhs = some rhsChecked)
    (hEval :
      (L03_GeneratedYul.Expr.add lhs rhs).Eval
        (SharedSemantics.addWord lhsChecked.value rhsChecked.value)) :
    compileExpr? (L03_GeneratedYul.Expr.add lhs rhs) =
      some
        (lhsChecked.code ++
          (rhsChecked.code ++
            [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add])) := by
  have hEvalEq :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.add [lhs, rhs]).eval? =
        some (SharedSemantics.addWord lhsChecked.value rhsChecked.value) := by
    simpa [L03_GeneratedYul.Expr.Eval, L03_GeneratedYul.Expr.add] using
      hEval
  simp [compileExpr?, compileExprChecked?, L03_GeneratedYul.Expr.add,
    hLhs, hRhs, hEvalEq, CheckedExpr.add]

theorem compileExpr?_addWords_eq
    {lhs rhs : L03_GeneratedYul.Word}
    (hEval :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.add
          [L03_GeneratedYul.Expr.word lhs,
            L03_GeneratedYul.Expr.word rhs]).eval? =
        some
          (SharedSemantics.addWord
            (SharedSemantics.norm lhs) (SharedSemantics.norm rhs))) :
    compileExpr?
        (L03_GeneratedYul.Expr.builtin
          SolidCoreYulCore.Evm.Builtin.add
            [L03_GeneratedYul.Expr.word lhs,
              L03_GeneratedYul.Expr.word rhs]) =
      some
        [ L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
        , L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm rhs))
        , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ] := by
  simp [compileExpr?, compileExprChecked?, CheckedExpr.add,
    CheckedExpr.word, hEval]

theorem compileExpr?_nestedAdd1And2And3_eq :
    compileExpr?
        (L03_GeneratedYul.Expr.add L03_GeneratedYul.Expr.add1And2
          L03_GeneratedYul.Expr.word3) =
      some
        [ L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 1)
        , L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 2)
        , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add
        , L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 3)
        , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ] := by
  have hLhs :
      compileExprChecked? L03_GeneratedYul.Expr.add1And2 =
        some CheckedExpr.add1And2 := by
    rfl
  have hRhs :
      compileExprChecked? L03_GeneratedYul.Expr.word3 =
        some (CheckedExpr.word 3) := by
    rfl
  have hEval :
      (L03_GeneratedYul.Expr.add L03_GeneratedYul.Expr.add1And2
        L03_GeneratedYul.Expr.word3).Eval
        (SharedSemantics.addWord CheckedExpr.add1And2.value
          (CheckedExpr.word 3).value) := by
    rfl
  simpa [CheckedExpr.add1And2, CheckedExpr.word,
    SharedSemantics.addWord, SharedSemantics.norm,
    SharedSemantics.wordModulus] using
  compileExpr?_addChecked_eq hLhs hRhs hEval

def compileReturnedExprArtifact? (program : L03_GeneratedYul.Program) :
    Option Artifact :=
  match program.returnedExpr? with
  | none => none
  | some expr =>
      match compileExprChecked? expr with
      | none => none
      | some checked => some (Artifact.returnChecked checked)

noncomputable def compile? (program : L03_GeneratedYul.Program) :
    Option Artifact := by
  classical
  exact
    if program = L03_GeneratedYul.Program.stop then
      some Artifact.stop
    else
      match returnBlockStmts? program with
      | some stmts =>
          match compileReturnBlockProgramArtifact? stmts with
          | some artifact => some artifact
          | none => compileReturnedExprArtifact? program
      | none => compileReturnedExprArtifact? program

inductive AcceptedProgram : L03_GeneratedYul.Program -> Prop where
  | stop {program : L03_GeneratedYul.Program} :
      program.IsStop ->
      AcceptedProgram program
  | returned {program : L03_GeneratedYul.Program}
      {expr : L03_GeneratedYul.Expr} {value : L03_GeneratedYul.Word} :
      program.returnedExpr? = some expr ->
      AcceptedExpr expr value ->
      AcceptedProgram program

noncomputable def acceptProgram? (program : L03_GeneratedYul.Program) :
    Bool := by
  classical
  exact
    if _hStop : program.IsStop then
      true
    else
      match program.returnedExpr? with
      | none => false
      | some expr =>
          match acceptExpr? expr with
          | some _ => true
          | none => false

theorem acceptProgram?_sound
    {program : L03_GeneratedYul.Program}
    (hAccept : acceptProgram? program = true) :
    AcceptedProgram program := by
  classical
  by_cases hStop : program.IsStop
  · exact AcceptedProgram.stop hStop
  · simp [acceptProgram?, hStop] at hAccept
    cases hReturned : program.returnedExpr? with
    | none =>
        simp [hReturned] at hAccept
    | some expr =>
        simp [hReturned] at hAccept
        cases hExpr : acceptExpr? expr with
        | none =>
            simp [hExpr] at hAccept
        | some value =>
            exact AcceptedProgram.returned hReturned
              (acceptExpr?_sound hExpr)

theorem acceptProgram?_complete
    {program : L03_GeneratedYul.Program}
    (hAccepted : AcceptedProgram program) :
    acceptProgram? program = true := by
  classical
  cases hAccepted with
  | stop hStop =>
      simp [acceptProgram?, hStop]
  | returned hReturned hExprAccepted =>
      by_cases hStop : program.IsStop
      · simp [acceptProgram?, hStop]
      · have hExpr := acceptExpr?_complete hExprAccepted
        simp [acceptProgram?, hStop, hReturned, hExpr]

structure SoundnessBoundary
    (_program : L03_GeneratedYul.Program) (_artifact : Artifact) :
    Prop where
  sourceWF : L03_GeneratedYul.WF _program
  artifactWF : L04_StackCfg.WF _artifact.program
  preservesBehavior :
    ∀ {behavior : L01_ValidSolidity.Behavior},
    L03_GeneratedYul.Semantics _program
        behavior ->
      L04_StackCfg.Semantics _artifact.program behavior
  artifactPseudoFree :
    _artifact.program.BlocksPseudoFree
  returnCodeStackDepth :
    ∀ {code : List L04_StackCfg.Instr},
      _artifact.program.IsReturnCode code ->
        L04_StackCfg.stackDepthAfter? 0 code = some 1

theorem soundnessBoundary_of_returnedExprChecked
    {program : L03_GeneratedYul.Program}
    {expr : L03_GeneratedYul.Expr}
    (hReturned : program.returnedExpr? = some expr)
    (checked : CheckedExpr expr) :
    SoundnessBoundary program (Artifact.returnChecked checked) := by
  let hStop := L03_GeneratedYul.Program.ne_stop_of_returnedExpr hReturned
  exact
    { sourceWF :=
        L03_GeneratedYul.Program.wf_of_returnedExpr hReturned
      artifactWF :=
        L04_StackCfg.Program.returnCode_wf checked.pseudoFree
          (checked.stackDepth 0)
      preservesBehavior := by
        intro behavior hSource
        cases hSource with
        | stop hProgram =>
            exact False.elim
              (hStop
                (L03_GeneratedYul.Program.eq_stop_of_isStop hProgram))
        | returnWord0 hReturn =>
            have hSourceValue :
                program.IsReturnValue 0 :=
              L03_GeneratedYul.Program.isReturnValue_of_isReturnWord0
                hReturn
            have hEq :=
              L03_GeneratedYul.Program.IsReturnValue.value_eq
                hReturned checked.eval hSourceValue
            have hSem :=
              L04_StackCfg.Program.returnCode_semantics
                (checked.exec [])
            rw [← hEq] at hSem
            exact hSem
        | returnWord3 hReturn =>
            have hSourceValue :
                program.IsReturnValue 3 :=
              L03_GeneratedYul.Program.isReturnValue_of_isReturnWord3
                hReturn
            have hEq :=
              L03_GeneratedYul.Program.IsReturnValue.value_eq
                hReturned checked.eval hSourceValue
            have hSem :=
              L04_StackCfg.Program.returnCode_semantics
                (checked.exec [])
            rw [← hEq] at hSem
            exact hSem
        | returnValue hReturn =>
            have hEq :=
              L03_GeneratedYul.Program.IsReturnValue.value_eq
                hReturned checked.eval hReturn
            have hSem :=
              L04_StackCfg.Program.returnCode_semantics
                (checked.exec [])
            rw [← hEq] at hSem
            exact hSem
      artifactPseudoFree :=
        L04_StackCfg.Program.returnCode_blocksPseudoFree
          checked.pseudoFree
      returnCodeStackDepth := by
        intro code hReturnCode
        have hCode :=
          L04_StackCfg.Program.returnCode_isReturnCode_code_eq
            hReturnCode
        subst code
        simpa using checked.stackDepth 0 }

theorem soundnessBoundary_of_returnBlockStmtsChecked
    {program : L03_GeneratedYul.Program}
    {stmts : List L03_GeneratedYul.Stmt}
    (hBlock : returnBlockStmts? program = some stmts)
    (checked : CheckedReturnStmts stmts) :
    SoundnessBoundary program (Artifact.returnStmtsChecked checked) := by
  have hProgramEq := returnBlockStmts?_eq_returnStmt hBlock
  rcases checked.sourceReturn with ⟨expr, hReturnedBlock, hEval⟩
  have hReturned : program.returnedExpr? = some expr := by
    rw [hProgramEq]
    simp [L03_GeneratedYul.Program.returnedExpr?,
      L03_GeneratedYul.Object.returnedExpr?,
      L03_GeneratedYul.Program.returnStmt,
      L03_GeneratedYul.Object.returnStmt,
      L03_GeneratedYul.Profile.empty, hReturnedBlock]
  let hStop := L03_GeneratedYul.Program.ne_stop_of_returnedExpr hReturned
  exact
    { sourceWF :=
        wf_of_returnBlockStmts? hBlock
      artifactWF :=
        by
          simpa [Artifact.returnStmtsChecked, Artifact.returnCode] using
            L04_StackCfg.Program.returnCode_wf
              checked.pseudoFree checked.stackDepth
      preservesBehavior := by
        intro behavior hSource
        cases hSource with
        | stop hProgram =>
            exact False.elim
              (hStop
                (L03_GeneratedYul.Program.eq_stop_of_isStop hProgram))
        | returnWord0 hReturn =>
            have hSourceValue :
                program.IsReturnValue 0 :=
              L03_GeneratedYul.Program.isReturnValue_of_isReturnWord0
                hReturn
            have hEq :=
              L03_GeneratedYul.Program.IsReturnValue.value_eq
                hReturned hEval hSourceValue
            have hSem := Artifact.returnStmtsChecked_semantics checked
            rw [← hEq] at hSem
            exact hSem
        | returnWord3 hReturn =>
            have hSourceValue :
                program.IsReturnValue 3 :=
              L03_GeneratedYul.Program.isReturnValue_of_isReturnWord3
                hReturn
            have hEq :=
              L03_GeneratedYul.Program.IsReturnValue.value_eq
                hReturned hEval hSourceValue
            have hSem := Artifact.returnStmtsChecked_semantics checked
            rw [← hEq] at hSem
            exact hSem
        | returnValue hReturn =>
            have hEq :=
              L03_GeneratedYul.Program.IsReturnValue.value_eq
                hReturned hEval hReturn
            have hSem := Artifact.returnStmtsChecked_semantics checked
            rw [← hEq] at hSem
            exact hSem
      artifactPseudoFree := by
        simpa [Artifact.returnStmtsChecked, Artifact.returnCode] using
          L04_StackCfg.Program.returnCode_blocksPseudoFree
            checked.pseudoFree
      returnCodeStackDepth := by
        intro code hReturnCode
        have hCode :=
          L04_StackCfg.Program.returnCode_isReturnCode_code_eq
            hReturnCode
        subst code
        simpa [Artifact.returnStmtsChecked, Artifact.returnCode] using
          checked.stackDepth }

theorem compile?_sound
    {program : L03_GeneratedYul.Program} {artifact : Artifact}
    (hCompile : compile? program = some artifact) :
    SoundnessBoundary program artifact := by
  classical
  by_cases hStop : program = L03_GeneratedYul.Program.stop
  · simp [compile?, hStop] at hCompile
    cases hCompile
    subst program
    exact
      { sourceWF := L03_GeneratedYul.Program.stop_wf
        artifactWF := L04_StackCfg.Program.stop_wf
        preservesBehavior := by
          intro behavior hSource
          cases hSource with
          | stop _ =>
              exact L04_StackCfg.Program.stop_semantics
          | returnWord0 hReturn =>
              exact False.elim
                (L03_GeneratedYul.Program.stop_not_isReturnValue
                  (L03_GeneratedYul.Program.isReturnValue_of_isReturnWord0
                    hReturn))
          | returnWord3 hReturn =>
              exact False.elim
                (L03_GeneratedYul.Program.stop_not_isReturnValue
                  (L03_GeneratedYul.Program.isReturnValue_of_isReturnWord3
                    hReturn))
          | returnValue hReturn =>
              exact False.elim
                (L03_GeneratedYul.Program.stop_not_isReturnValue hReturn)
        artifactPseudoFree :=
          L04_StackCfg.Program.stop_blocksPseudoFree
        returnCodeStackDepth := by
          intro code hReturnCode
          exact False.elim
            (L04_StackCfg.Program.stop_not_isReturnCode hReturnCode) }
  · simp [compile?, hStop] at hCompile
    cases hBlock : returnBlockStmts? program with
    | some stmts =>
        cases hBlockArtifact :
            compileReturnBlockProgramArtifact? stmts with
        | some blockArtifact =>
            simp [hBlock, hBlockArtifact] at hCompile
            cases hCompile
            cases hChecked : compileReturnStmtsChecked? stmts with
            | none =>
                simp [compileReturnBlockProgramArtifact?,
                  compileReturnStmtsArtifact?, hChecked] at hBlockArtifact
            | some checked =>
                simp [compileReturnBlockProgramArtifact?,
                  compileReturnStmtsArtifact?, hChecked] at hBlockArtifact
                cases hBlockArtifact
                exact
                  soundnessBoundary_of_returnBlockStmtsChecked
                    hBlock checked
        | none =>
            simp [hBlock, hBlockArtifact, compileReturnedExprArtifact?]
              at hCompile
            cases hReturned : program.returnedExpr? with
            | none =>
                simp [hReturned] at hCompile
            | some expr =>
                cases hChecked : compileExprChecked? expr with
                | none =>
                    simp [hReturned, hChecked] at hCompile
                | some checked =>
                    simp [hReturned, hChecked] at hCompile
                    cases hCompile
                    exact
                      soundnessBoundary_of_returnedExprChecked
                        hReturned checked
    | none =>
        simp [hBlock, compileReturnedExprArtifact?] at hCompile
        cases hReturned : program.returnedExpr? with
        | none =>
            simp [hReturned] at hCompile
        | some expr =>
            cases hChecked : compileExprChecked? expr with
            | none =>
                simp [hReturned, hChecked] at hCompile
            | some checked =>
                simp [hReturned, hChecked] at hCompile
                cases hCompile
                exact
                  soundnessBoundary_of_returnedExprChecked
                    hReturned checked

theorem compile?_complete_for_stop
    {program : L03_GeneratedYul.Program}
    (hStop : program.IsStop) :
    ∃ artifact, compile? program = some artifact := by
  classical
  have hProgram := L03_GeneratedYul.Program.eq_stop_of_isStop hStop
  subst program
  exact ⟨Artifact.stop, by simp [compile?, Artifact.stop]⟩

theorem compile?_stop_eq :
    compile? L03_GeneratedYul.Program.stop = some Artifact.stop := by
  simp [compile?, Artifact.stop]

theorem compile?_returnCheckedExpr_eq
    {program : L03_GeneratedYul.Program}
    {expr : L03_GeneratedYul.Expr} {checked : CheckedExpr expr}
    (hReturned : program.returnedExpr? = some expr)
    (hChecked : compileExprChecked? expr = some checked)
    (hBlock : returnBlockStmts? program = none) :
    compile? program =
      some (Artifact.returnChecked checked) := by
  classical
  have hStop := L03_GeneratedYul.Program.ne_stop_of_returnedExpr hReturned
  simp [compile?, hStop, hBlock, compileReturnedExprArtifact?,
    hReturned, hChecked, Artifact.returnChecked, Artifact.returnCode]

theorem compile?_complete_for_returnedCheckedExpr
    {program : L03_GeneratedYul.Program}
    {expr : L03_GeneratedYul.Expr} {checked : CheckedExpr expr}
    (hReturned : program.returnedExpr? = some expr)
    (hChecked : compileExprChecked? expr = some checked) :
    ∃ artifact, compile? program = some artifact := by
  classical
  have hStop := L03_GeneratedYul.Program.ne_stop_of_returnedExpr hReturned
  cases hBlock : returnBlockStmts? program with
  | none =>
      exact ⟨Artifact.returnChecked checked,
        compile?_returnCheckedExpr_eq hReturned hChecked hBlock⟩
  | some stmts =>
      cases hArtifact : compileReturnBlockProgramArtifact? stmts with
      | none =>
          exact
            ⟨Artifact.returnChecked checked,
              by
                simp [compile?, hStop, hBlock, hArtifact,
                  compileReturnedExprArtifact?, hReturned, hChecked,
                  Artifact.returnChecked, Artifact.returnCode]⟩
      | some artifact =>
          exact
            ⟨artifact,
              by simp [compile?, hStop, hBlock, hArtifact]⟩

theorem compile?_returnBlockStmtsChecked_eq
    {program : L03_GeneratedYul.Program}
    {stmts : List L03_GeneratedYul.Stmt}
    {checked : CheckedReturnStmts stmts}
    (hBlock : returnBlockStmts? program = some stmts)
    (hChecked : compileReturnStmtsChecked? stmts = some checked) :
    compile? program = some (Artifact.returnStmtsChecked checked) := by
  classical
  have hStop : program ≠ L03_GeneratedYul.Program.stop := by
    intro hProgram
    subst program
    simp [returnBlockStmts?, L03_GeneratedYul.Program.stop,
      L03_GeneratedYul.Object.stop, L03_GeneratedYul.Profile.empty]
      at hBlock
  simp [compile?, hStop, hBlock,
    compileReturnBlockProgramArtifact?, compileReturnStmtsArtifact?,
    hChecked]

theorem compile?_neutralAddPrefixReturnWord_program_eq
    (lhs rhs value : L03_GeneratedYul.Word) :
    Option.map Artifact.program
      (compile?
        (L03_GeneratedYul.Program.returnStmt
          (L03_GeneratedYul.Stmt.block
            [ L03_GeneratedYul.Stmt.expr
                (L03_GeneratedYul.Expr.add
                  (L03_GeneratedYul.Expr.word lhs)
                  (L03_GeneratedYul.Expr.word rhs))
            , L03_GeneratedYul.Stmt.expr
                (L03_GeneratedYul.Expr.builtin
                  SolidCoreYulCore.Evm.Builtin.mstore
                  [L03_GeneratedYul.Expr.word 0,
                    L03_GeneratedYul.Expr.word value])
            , L03_GeneratedYul.Stmt.expr
                (L03_GeneratedYul.Expr.builtin
                  SolidCoreYulCore.Evm.Builtin.returnOp
                  [L03_GeneratedYul.Expr.word 0,
                    L03_GeneratedYul.Expr.word 32]) ]))) =
      some
        (L04_StackCfg.Program.returnCode
          [ L04_StackCfg.Instr.push
              (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
          , L04_StackCfg.Instr.push
              (L04_StackCfg.Atom.word (SharedSemantics.norm rhs))
          , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add
          , L04_StackCfg.Instr.pop
          , L04_StackCfg.Instr.push
              (L04_StackCfg.Atom.word (SharedSemantics.norm value)) ]) := by
  have hEval :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.add
          [L03_GeneratedYul.Expr.word lhs,
            L03_GeneratedYul.Expr.word rhs]).eval? =
        some
          (SharedSemantics.addWord
            (SharedSemantics.norm lhs) (SharedSemantics.norm rhs)) := by
    rfl
  simp [compile?, returnBlockStmts?,
    compileReturnBlockProgramArtifact?, compileReturnStmtsArtifact?,
    compileReturnStmtsChecked?, compileNeutralStmtChecked?,
    compileDiscardedExprChecked?, compileExprChecked?,
    CheckedDiscardedExpr.ofChecked, CheckedNeutralStmt.expr,
    CheckedReturnStmts.cons, CheckedReturnStmts.returnedBlock,
    Artifact.returnStmtsChecked, Artifact.returnCode,
    L03_GeneratedYul.Program.returnStmt,
    L03_GeneratedYul.Object.returnStmt,
    L03_GeneratedYul.Profile.empty,
    L03_GeneratedYul.Program.stop,
    L03_GeneratedYul.Object.stop,
    L03_GeneratedYul.Expr.add,
    CheckedExpr.add, CheckedExpr.word, hEval]

theorem compile?_let1ReturnVar_program_eq
    (name value : L03_GeneratedYul.Word) :
    Option.map Artifact.program
      (compile?
        (L03_GeneratedYul.Program.let1ReturnVar name value)) =
      some
        (L04_StackCfg.Program.returnCode
          [L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm value))]) := by
  simp [compile?, returnBlockStmts?,
    compileReturnBlockProgramArtifact?, compileReturnStmtsArtifact?,
    compileReturnStmtsChecked?, compileNeutralStmtChecked?,
    compileReturnedExprArtifact?,
    compileExprChecked?, Artifact.returnChecked, Artifact.returnCode,
    L03_GeneratedYul.Program.let1ReturnVar,
    L03_GeneratedYul.Stmt.let1ReturnVar,
    L03_GeneratedYul.Program.returnStmt,
    L03_GeneratedYul.Object.returnStmt,
    L03_GeneratedYul.Program.stop,
    L03_GeneratedYul.Object.stop,
    L03_GeneratedYul.Profile.empty,
    L03_GeneratedYul.Program.returnedExpr?,
    L03_GeneratedYul.Object.returnedExpr?,
    L03_GeneratedYul.Stmt.returnedExpr?,
    L03_GeneratedYul.Stmt.returnedExprs?,
    L03_GeneratedYul.Stmt.returnedExprWithLocals?,
    L03_GeneratedYul.Stmt.returnedExprsWithLocals?,
    L03_GeneratedYul.Stmt.stepLocal?,
    L03_GeneratedYul.Stmt.neutral?,
    L03_GeneratedYul.Expr.evalWith?,
    L03_GeneratedYul.Env.declare?,
    L03_GeneratedYul.Env.contains,
    L03_GeneratedYul.Env.lookup?,
    CheckedExpr.word, SharedSemantics.norm_norm]

theorem acceptProgram?_let1ReturnVar
    (name value : L03_GeneratedYul.Word) :
    acceptProgram? (L03_GeneratedYul.Program.let1ReturnVar name value) =
      true := by
  have hReturned :
      (L03_GeneratedYul.Program.let1ReturnVar name value).returnedExpr? =
        some (L03_GeneratedYul.Expr.word
          (SharedSemantics.norm value)) :=
    L03_GeneratedYul.Program.let1ReturnVar_returnedExpr? name value
  have hNotStop :
      ¬ (L03_GeneratedYul.Program.let1ReturnVar name value).IsStop := by
    intro hStop
    exact L03_GeneratedYul.Program.ne_stop_of_returnedExpr hReturned
      (L03_GeneratedYul.Program.eq_stop_of_isStop hStop)
  simp [acceptProgram?, hNotStop, hReturned, acceptExpr?,
    acceptExprChecked?, SharedSemantics.norm_norm]

theorem compile?_memoryRoundTripReturn_program_eq
    (value : L03_GeneratedYul.Word) :
    Option.map Artifact.program
      (compile?
        (L03_GeneratedYul.Program.memoryRoundTripReturn value)) =
      some
        (L04_StackCfg.Program.returnCode
          [L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm value))]) := by
  simp [compile?, returnBlockStmts?,
    compileReturnBlockProgramArtifact?, compileReturnStmtsArtifact?,
    compileReturnStmtsChecked?, compileNeutralStmtChecked?,
    compileDiscardedExprChecked?, compileReturnedExprArtifact?,
    compileExprChecked?, Artifact.returnChecked, Artifact.returnCode,
    L03_GeneratedYul.Program.memoryRoundTripReturn,
    L03_GeneratedYul.Stmt.memoryRoundTripReturn,
    L03_GeneratedYul.Program.returnStmt,
    L03_GeneratedYul.Object.returnStmt,
    L03_GeneratedYul.Program.stop,
    L03_GeneratedYul.Object.stop,
    L03_GeneratedYul.Profile.empty,
    L03_GeneratedYul.Program.returnedExpr?,
    L03_GeneratedYul.Object.returnedExpr?,
    L03_GeneratedYul.Stmt.returnedExpr?,
    L03_GeneratedYul.Stmt.returnedExprs?,
    L03_GeneratedYul.Stmt.returnedExprWithLocals?,
    L03_GeneratedYul.Stmt.returnedExprsWithLocals?,
    L03_GeneratedYul.Stmt.returnedExprWithState?,
    L03_GeneratedYul.Stmt.returnedExprsWithState?,
    L03_GeneratedYul.Stmt.stepLocal?,
    L03_GeneratedYul.Stmt.stepState?,
    L03_GeneratedYul.Stmt.neutral?,
    L03_GeneratedYul.Stmt.mstore,
    L03_GeneratedYul.Stmt.returnMemory,
    L03_GeneratedYul.Expr.evalWith?,
    L03_GeneratedYul.Expr.evalWithState?,
    L03_GeneratedYul.Expr.mload,
    L03_GeneratedYul.Memory.store,
    L03_GeneratedYul.Memory.lookup?,
    L03_GeneratedYul.State.empty,
    L03_GeneratedYul.Expr.word0,
    L03_GeneratedYul.Expr.word32,
    CheckedExpr.word, SharedSemantics.norm, SharedSemantics.wordModulus]

theorem acceptProgram?_memoryRoundTripReturn
    (value : L03_GeneratedYul.Word) :
    acceptProgram?
      (L03_GeneratedYul.Program.memoryRoundTripReturn value) = true := by
  have hReturned :
      (L03_GeneratedYul.Program.memoryRoundTripReturn value).returnedExpr? =
        some (L03_GeneratedYul.Expr.word
          (SharedSemantics.norm value)) :=
    L03_GeneratedYul.Program.memoryRoundTripReturn_returnedExpr? value
  have hNotStop :
      ¬ (L03_GeneratedYul.Program.memoryRoundTripReturn value).IsStop := by
    intro hStop
    exact L03_GeneratedYul.Program.ne_stop_of_returnedExpr hReturned
      (L03_GeneratedYul.Program.eq_stop_of_isStop hStop)
  simp [acceptProgram?, hNotStop, hReturned, acceptExpr?,
    acceptExprChecked?, SharedSemantics.norm_norm]

theorem compile?_ifZeroFallthroughReturn_program_eq
    (value : L03_GeneratedYul.Word) :
    Option.map Artifact.program
      (compile?
        (L03_GeneratedYul.Program.ifZeroFallthroughReturn value)) =
      some
        (L04_StackCfg.Program.returnCode
          [L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm value))]) := by
  simp [compile?, returnBlockStmts?,
    compileReturnBlockProgramArtifact?, compileReturnStmtsArtifact?,
    compileReturnStmtsChecked?, compileNeutralStmtChecked?,
    compileReturnedExprArtifact?,
    compileExprChecked?, Artifact.returnChecked, Artifact.returnCode,
    L03_GeneratedYul.Program.ifZeroFallthroughReturn,
    L03_GeneratedYul.Stmt.ifZeroFallthroughReturn,
    L03_GeneratedYul.Program.returnStmt,
    L03_GeneratedYul.Object.returnStmt,
    L03_GeneratedYul.Program.stop,
    L03_GeneratedYul.Object.stop,
    L03_GeneratedYul.Profile.empty,
    L03_GeneratedYul.Program.returnedExpr?,
    L03_GeneratedYul.Object.returnedExpr?,
    L03_GeneratedYul.Stmt.returnWord,
    L03_GeneratedYul.Stmt.returnExpr,
    L03_GeneratedYul.Stmt.returnedExpr?,
    L03_GeneratedYul.Stmt.returnedExprs?,
    L03_GeneratedYul.Stmt.returnedExprWithLocals?,
    L03_GeneratedYul.Stmt.returnedExprsWithLocals?,
    L03_GeneratedYul.Stmt.returnedExprWithState?,
    L03_GeneratedYul.Stmt.returnedExprsWithState?,
    L03_GeneratedYul.Stmt.stepLocal?,
    L03_GeneratedYul.Stmt.stepState?,
    L03_GeneratedYul.Stmt.neutral?,
    L03_GeneratedYul.Expr.evalWithState?,
    L03_GeneratedYul.Memory.store,
    L03_GeneratedYul.Memory.lookup?,
    L03_GeneratedYul.State.empty,
    L03_GeneratedYul.Expr.word0,
    L03_GeneratedYul.Expr.word32,
    CheckedExpr.word, SharedSemantics.norm, SharedSemantics.wordModulus]

theorem acceptProgram?_ifZeroFallthroughReturn
    (value : L03_GeneratedYul.Word) :
    acceptProgram?
      (L03_GeneratedYul.Program.ifZeroFallthroughReturn value) = true := by
  have hReturned :
      (L03_GeneratedYul.Program.ifZeroFallthroughReturn value).returnedExpr? =
        some (L03_GeneratedYul.Expr.word
          (SharedSemantics.norm value)) :=
    L03_GeneratedYul.Program.ifZeroFallthroughReturn_returnedExpr? value
  have hNotStop :
      ¬ (L03_GeneratedYul.Program.ifZeroFallthroughReturn value).IsStop := by
    intro hStop
    exact L03_GeneratedYul.Program.ne_stop_of_returnedExpr hReturned
      (L03_GeneratedYul.Program.eq_stop_of_isStop hStop)
  simp [acceptProgram?, hNotStop, hReturned, acceptExpr?,
    acceptExprChecked?, SharedSemantics.norm_norm]

theorem compile?_switchZeroReturn_program_eq
    (value fallback : L03_GeneratedYul.Word) :
    Option.map Artifact.program
      (compile?
        (L03_GeneratedYul.Program.switchZeroReturn value fallback)) =
      some
        (L04_StackCfg.Program.returnCode
          [L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm value))]) := by
  simp [compile?, returnBlockStmts?,
    compileReturnedExprArtifact?,
    compileExprChecked?, Artifact.returnChecked, Artifact.returnCode,
    L03_GeneratedYul.Program.switchZeroReturn,
    L03_GeneratedYul.Stmt.switchZeroReturn,
    L03_GeneratedYul.Program.returnStmt,
    L03_GeneratedYul.Object.returnStmt,
    L03_GeneratedYul.Program.stop,
    L03_GeneratedYul.Object.stop,
    L03_GeneratedYul.Profile.empty,
    L03_GeneratedYul.Program.returnedExpr?,
    L03_GeneratedYul.Object.returnedExpr?,
    L03_GeneratedYul.Stmt.returnWord,
    L03_GeneratedYul.Stmt.returnExpr,
    L03_GeneratedYul.Stmt.returnedExpr?,
    L03_GeneratedYul.Stmt.returnedExprs?,
    L03_GeneratedYul.Expr.eval?,
    L03_GeneratedYul.Expr.evalWith?,
    L03_GeneratedYul.Expr.word0,
    L03_GeneratedYul.Expr.word32,
    CheckedExpr.word, SharedSemantics.norm, SharedSemantics.wordModulus]

theorem acceptProgram?_switchZeroReturn
    (value fallback : L03_GeneratedYul.Word) :
    acceptProgram?
      (L03_GeneratedYul.Program.switchZeroReturn value fallback) = true := by
  have hReturned :
      (L03_GeneratedYul.Program.switchZeroReturn value fallback).returnedExpr? =
        some (L03_GeneratedYul.Expr.word value) :=
    L03_GeneratedYul.Program.switchZeroReturn_returnedExpr? value fallback
  have hNotStop :
      ¬ (L03_GeneratedYul.Program.switchZeroReturn value fallback).IsStop := by
    intro hStop
    exact L03_GeneratedYul.Program.ne_stop_of_returnedExpr hReturned
      (L03_GeneratedYul.Program.eq_stop_of_isStop hStop)
  simp [acceptProgram?, hNotStop, hReturned, acceptExpr?,
    acceptExprChecked?]

theorem compile?_sound_for_acceptReturnBlockStmts?
    {program : L03_GeneratedYul.Program}
    {stmts : List L03_GeneratedYul.Stmt}
    {value : L03_GeneratedYul.Word}
    (_hReturned : program.returnedExpr? = none)
    (hBlock : returnBlockStmts? program = some stmts)
    (hAccept : acceptReturnStmts? stmts = some value) :
    ∃ artifact,
      compile? program = some artifact ∧
        SoundnessBoundary program artifact ∧
        L04_StackCfg.Semantics artifact.program
          (L01_ValidSolidity.Behavior.returnedWord value) := by
  rcases compileReturnStmtsChecked?_complete_for_accepted
      (acceptReturnStmts?_sound hAccept) with
    ⟨checked, hChecked, hValue⟩
  refine
    ⟨Artifact.returnStmtsChecked checked, ?_, ?_, ?_⟩
  · exact compile?_returnBlockStmtsChecked_eq
      hBlock hChecked
  · exact compile?_sound
      (compile?_returnBlockStmtsChecked_eq hBlock hChecked)
  · cases hValue
    exact Artifact.returnStmtsChecked_semantics checked

theorem compile?_complete_for_accepted
    {program : L03_GeneratedYul.Program}
    (hAccepted : AcceptedProgram program) :
    ∃ artifact, compile? program = some artifact := by
  cases hAccepted with
  | stop hStop =>
      exact compile?_complete_for_stop hStop
  | returned hReturned hExprAccepted =>
      rcases compileExprChecked?_complete_for_accepted hExprAccepted with
        ⟨checked, hChecked, _hValue⟩
      exact compile?_complete_for_returnedCheckedExpr hReturned hChecked

theorem compile?_sound_for_accepted
    {program : L03_GeneratedYul.Program}
    (hAccepted : AcceptedProgram program) :
    ∃ artifact,
      compile? program = some artifact ∧
        SoundnessBoundary program artifact := by
  rcases compile?_complete_for_accepted hAccepted with
    ⟨artifact, hCompile⟩
  exact ⟨artifact, hCompile, compile?_sound hCompile⟩

theorem compile?_sound_for_acceptProgram?
    {program : L03_GeneratedYul.Program}
    (hAccept : acceptProgram? program = true) :
    ∃ artifact,
      compile? program = some artifact ∧
        SoundnessBoundary program artifact := by
  exact compile?_sound_for_accepted (acceptProgram?_sound hAccept)

theorem compile?_returnExprChecked_eq
    {expr : L03_GeneratedYul.Expr} {checked : CheckedExpr expr}
    (hChecked : compileExprChecked? expr = some checked) :
    compile? (L03_GeneratedYul.Program.returnExpr expr) =
      some (Artifact.returnChecked checked) := by
  simp [compile?, returnBlockStmts?,
    compileReturnBlockProgramArtifact?, compileReturnStmtsArtifact?,
    compileReturnStmtsChecked?, compileNeutralStmtChecked?,
    compileDiscardedExprChecked?, compileExprChecked?,
    L03_GeneratedYul.Program.returnExpr,
    L03_GeneratedYul.Program.returnStmt,
    L03_GeneratedYul.Object.returnStmt,
    L03_GeneratedYul.Stmt.returnExpr,
    L03_GeneratedYul.Program.stop,
    L03_GeneratedYul.Object.stop,
    L03_GeneratedYul.Profile.empty,
    L03_GeneratedYul.Expr.word0,
    L03_GeneratedYul.Expr.word32,
    hChecked]

theorem compile?_complete_for_returnExprChecked
    {expr : L03_GeneratedYul.Expr} {checked : CheckedExpr expr}
    (hChecked : compileExprChecked? expr = some checked) :
    ∃ artifact,
      compile? (L03_GeneratedYul.Program.returnExpr expr) = some artifact := by
  exact compile?_complete_for_returnedCheckedExpr (by rfl) hChecked

theorem compile?_returnExprChecked_stackDepth
    {expr : L03_GeneratedYul.Expr} {checked : CheckedExpr expr}
    (hChecked : compileExprChecked? expr = some checked)
    (depth : Nat) :
    L04_StackCfg.stackDepthAfter? depth checked.code = some (depth + 1) := by
  have _ := hChecked
  exact checked.stackDepth depth

theorem compile?_returnAddChecked_eq
    {lhs rhs : L03_GeneratedYul.Expr}
    {lhsChecked : CheckedExpr lhs} {rhsChecked : CheckedExpr rhs}
    (hLhs : compileExprChecked? lhs = some lhsChecked)
    (hRhs : compileExprChecked? rhs = some rhsChecked)
    (hEval :
      (L03_GeneratedYul.Expr.add lhs rhs).Eval
        (SharedSemantics.addWord lhsChecked.value rhsChecked.value)) :
    compile?
        (L03_GeneratedYul.Program.returnExpr
          (L03_GeneratedYul.Expr.add lhs rhs)) =
      some
        (Artifact.returnCode
          (lhsChecked.code ++
            (rhsChecked.code ++
              [L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add]))
          (CheckedExpr.addCodePseudoFree lhsChecked rhsChecked)
          ((CheckedExpr.add lhsChecked rhsChecked hEval).stackDepth 0)) := by
  have hEvalEq :
      (L03_GeneratedYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.add [lhs, rhs]).eval? =
        some (SharedSemantics.addWord lhsChecked.value rhsChecked.value) := by
    simpa [L03_GeneratedYul.Expr.Eval, L03_GeneratedYul.Expr.add] using
      hEval
  have hChecked :
      compileExprChecked? (L03_GeneratedYul.Expr.add lhs rhs) =
        some (CheckedExpr.add lhsChecked rhsChecked hEval) := by
    simp [compileExprChecked?, L03_GeneratedYul.Expr.add,
      hLhs, hRhs, hEvalEq, CheckedExpr.add]
  simpa [Artifact.returnChecked, Artifact.returnCode,
    CheckedExpr.add] using
    compile?_returnExprChecked_eq hChecked

theorem compile?_returnWord_eq (value : L03_GeneratedYul.Word) :
    compile? (L03_GeneratedYul.Program.returnWord value) =
      some (Artifact.returnWord (SharedSemantics.norm value)) := by
  simpa [Artifact.returnChecked, Artifact.returnWord,
    Artifact.returnCode, CheckedExpr.word,
    L03_GeneratedYul.Program.returnWord,
    L03_GeneratedYul.Object.returnWord,
    L03_GeneratedYul.Stmt.returnWord] using
    compile?_returnExprChecked_eq
      (expr := L03_GeneratedYul.Expr.word value)
      (checked := CheckedExpr.word value)
      rfl

theorem compile?_complete_for_returnWord
    (value : L03_GeneratedYul.Word) :
    ∃ artifact,
      compile? (L03_GeneratedYul.Program.returnWord value) = some artifact := by
  exact ⟨Artifact.returnWord (SharedSemantics.norm value),
    compile?_returnWord_eq value⟩

theorem compile?_complete_for_isReturnWord
    {program : L03_GeneratedYul.Program} {value : L03_GeneratedYul.Word}
    (hReturn : program.IsReturnWord value) :
    ∃ artifact, compile? program = some artifact := by
  have hProgram :=
    L03_GeneratedYul.Program.eq_returnWord_of_isReturnWord hReturn
  subst program
  exact compile?_complete_for_returnWord value

theorem compile?_returnWord0_eq :
    compile? L03_GeneratedYul.Program.returnWord0 =
      some (Artifact.returnWord 0) := by
  simpa [L03_GeneratedYul.Program.returnWord0,
    Artifact.returnWord, SharedSemantics.norm, SharedSemantics.norm,
    SharedSemantics.wordModulus] using
    compile?_returnWord_eq 0

theorem compile?_complete_for_returnWord0
    {program : L03_GeneratedYul.Program}
    (hReturn : program.IsReturnWord0) :
    ∃ artifact, compile? program = some artifact := by
  rcases hReturn with ⟨hObject, hProfile⟩
  rcases hObject with ⟨hCode, hFunctions, hData, hSubobjects⟩
  rcases hProfile with
    ⟨hLayout, hAbi, hEvents, hErrors, hMemoryRegions, hHelpers⟩
  cases program with
  | mk object profile =>
      cases object with
      | mk code functions data subobjects =>
          cases profile with
          | mk layout abi events errors memoryRegions emittedHelpers =>
              cases hCode
              cases hFunctions
              cases hData
              cases hSubobjects
              cases hLayout
              cases hAbi
              cases hEvents
              cases hErrors
              cases hMemoryRegions
              cases hHelpers
              exact ⟨Artifact.returnWord 0, compile?_returnWord0_eq⟩

theorem compile?_returnWord3_eq :
    compile? L03_GeneratedYul.Program.returnWord3 =
      some (Artifact.returnWord 3) := by
  simpa [L03_GeneratedYul.Program.returnWord3,
    Artifact.returnWord, SharedSemantics.norm, SharedSemantics.norm,
    SharedSemantics.wordModulus] using
    compile?_returnWord_eq 3

theorem compile?_complete_for_returnWord3
    {program : L03_GeneratedYul.Program}
    (hReturn : program.IsReturnWord3) :
    ∃ artifact, compile? program = some artifact := by
  rcases hReturn with ⟨hObject, hProfile⟩
  rcases hObject with ⟨hCode, hFunctions, hData, hSubobjects⟩
  rcases hProfile with
    ⟨hLayout, hAbi, hEvents, hErrors, hMemoryRegions, hHelpers⟩
  cases program with
  | mk object profile =>
      cases object with
      | mk code functions data subobjects =>
          cases profile with
          | mk layout abi events errors memoryRegions emittedHelpers =>
              cases hCode
              cases hFunctions
              cases hData
              cases hSubobjects
              cases hLayout
              cases hAbi
              cases hEvents
              cases hErrors
              cases hMemoryRegions
              cases hHelpers
              exact ⟨Artifact.returnWord 3, compile?_returnWord3_eq⟩

theorem compile?_returnAddWords_eq
    {lhs rhs : L03_GeneratedYul.Word}
    (hEval :
      (L03_GeneratedYul.Expr.add
        (L03_GeneratedYul.Expr.word lhs)
        (L03_GeneratedYul.Expr.word rhs)).Eval
        (SharedSemantics.addWord
          (SharedSemantics.norm lhs) (SharedSemantics.norm rhs))) :
    compile?
        (L03_GeneratedYul.Program.returnExpr
          (L03_GeneratedYul.Expr.add
            (L03_GeneratedYul.Expr.word lhs)
            (L03_GeneratedYul.Expr.word rhs))) =
      some
        (Artifact.returnCode
          [ L04_StackCfg.Instr.push
              (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
          , L04_StackCfg.Instr.push
              (L04_StackCfg.Atom.word (SharedSemantics.norm rhs))
          , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ]
          (pushPushAddPseudoFree
            (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
            (L04_StackCfg.Atom.word (SharedSemantics.norm rhs)))
          (pushPushAddStackDepth
            (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
            (L04_StackCfg.Atom.word (SharedSemantics.norm rhs)))) := by
  have hGeneric :
      compile?
          (L03_GeneratedYul.Program.returnExpr
            (L03_GeneratedYul.Expr.add
              (L03_GeneratedYul.Expr.word lhs)
              (L03_GeneratedYul.Expr.word rhs))) =
        some
          (Artifact.returnCode
            [ L04_StackCfg.Instr.push
                (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
            , L04_StackCfg.Instr.push
                (L04_StackCfg.Atom.word (SharedSemantics.norm rhs))
            , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ]
            (CheckedExpr.addCodePseudoFree
              (CheckedExpr.word lhs) (CheckedExpr.word rhs))
            ((CheckedExpr.add
              (CheckedExpr.word lhs) (CheckedExpr.word rhs) hEval).stackDepth 0)) := by
    simpa [CheckedExpr.word] using
      compile?_returnAddChecked_eq
        (lhsChecked := CheckedExpr.word lhs)
        (rhsChecked := CheckedExpr.word rhs)
        (by rfl) (by rfl) hEval
  exact hGeneric.trans
    (by
      apply congrArg some
      apply Artifact.ext_program
      rfl)

theorem compile?_complete_for_returnAddWords
    {lhs rhs : L03_GeneratedYul.Word}
    (hEval :
      (L03_GeneratedYul.Expr.add
        (L03_GeneratedYul.Expr.word lhs)
        (L03_GeneratedYul.Expr.word rhs)).Eval
        (SharedSemantics.addWord
          (SharedSemantics.norm lhs) (SharedSemantics.norm rhs))) :
    ∃ artifact,
      compile?
        (L03_GeneratedYul.Program.returnExpr
          (L03_GeneratedYul.Expr.add
            (L03_GeneratedYul.Expr.word lhs)
            (L03_GeneratedYul.Expr.word rhs))) = some artifact := by
  exact
    ⟨Artifact.returnCode
        [ L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
        , L04_StackCfg.Instr.push
            (L04_StackCfg.Atom.word (SharedSemantics.norm rhs))
        , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ]
        (pushPushAddPseudoFree
          (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
          (L04_StackCfg.Atom.word (SharedSemantics.norm rhs)))
        (pushPushAddStackDepth
          (L04_StackCfg.Atom.word (SharedSemantics.norm lhs))
          (L04_StackCfg.Atom.word (SharedSemantics.norm rhs))),
      compile?_returnAddWords_eq hEval⟩

theorem compile?_returnNestedAdd1And2And3_eq :
    compile?
        (L03_GeneratedYul.Program.returnExpr
          (L03_GeneratedYul.Expr.add L03_GeneratedYul.Expr.add1And2
            L03_GeneratedYul.Expr.word3)) =
      some
        (Artifact.returnCode
          [ L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 1)
          , L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 2)
          , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add
          , L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 3)
          , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ]
          (pushPushAddPushAddPseudoFree
            (L04_StackCfg.Atom.word 1)
            (L04_StackCfg.Atom.word 2)
            (L04_StackCfg.Atom.word 3))
          (pushPushAddPushAddStackDepth
            (L04_StackCfg.Atom.word 1)
            (L04_StackCfg.Atom.word 2)
            (L04_StackCfg.Atom.word 3))) := by
  have hLhs :
      compileExprChecked? L03_GeneratedYul.Expr.add1And2 =
        some CheckedExpr.add1And2 := by
    rfl
  have hRhs :
      compileExprChecked? L03_GeneratedYul.Expr.word3 =
        some (CheckedExpr.word 3) := by
    rfl
  have hEval :
      (L03_GeneratedYul.Expr.add L03_GeneratedYul.Expr.add1And2
        L03_GeneratedYul.Expr.word3).Eval
        (SharedSemantics.addWord CheckedExpr.add1And2.value
          (CheckedExpr.word 3).value) := by
    rfl
  simpa [CheckedExpr.add1And2, CheckedExpr.word,
    SharedSemantics.addWord, SharedSemantics.norm,
    SharedSemantics.wordModulus] using
    compile?_returnAddChecked_eq hLhs hRhs hEval

theorem compile?_complete_for_returnAdd1And2 :
    ∃ artifact,
      compile? L03_GeneratedYul.Program.returnAdd1And2 = some artifact := by
  have hEval :
      (L03_GeneratedYul.Expr.add
        (L03_GeneratedYul.Expr.word 1)
        (L03_GeneratedYul.Expr.word 2)).Eval
        (SharedSemantics.addWord
          (SharedSemantics.norm 1) (SharedSemantics.norm 2)) := by
    rfl
  simpa [L03_GeneratedYul.Program.returnAdd1And2,
    L03_GeneratedYul.Expr.add1And2,
    L03_GeneratedYul.Expr.word1,
    L03_GeneratedYul.Expr.word2,
    SharedSemantics.addWord, SharedSemantics.norm,
    SharedSemantics.wordModulus] using
    compile?_complete_for_returnAddWords hEval

theorem compile?_returnAdd1And2_eq :
    compile? L03_GeneratedYul.Program.returnAdd1And2 =
      some
        (Artifact.returnCode
          [ L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 1)
          , L04_StackCfg.Instr.push (L04_StackCfg.Atom.word 2)
          , L04_StackCfg.Instr.op L04_StackCfg.PrimOp.add ]
          (pushPushAddPseudoFree
            (L04_StackCfg.Atom.word 1)
            (L04_StackCfg.Atom.word 2))
          (pushPushAddStackDepth
            (L04_StackCfg.Atom.word 1)
            (L04_StackCfg.Atom.word 2))) := by
  have hEval :
      (L03_GeneratedYul.Expr.add
        (L03_GeneratedYul.Expr.word 1)
        (L03_GeneratedYul.Expr.word 2)).Eval
        (SharedSemantics.addWord
          (SharedSemantics.norm 1) (SharedSemantics.norm 2)) := by
    rfl
  simpa [L03_GeneratedYul.Program.returnAdd1And2,
    L03_GeneratedYul.Expr.add1And2,
    L03_GeneratedYul.Expr.word1,
    L03_GeneratedYul.Expr.word2,
    SharedSemantics.addWord, SharedSemantics.norm,
    SharedSemantics.wordModulus] using
    compile?_returnAddWords_eq (lhs := 1) (rhs := 2) hEval

end P04_GeneratedYulToStackCfg
end Passes
end Spine
end SolidCore
