import SolidCore.Solidity.Checked

/-! SolidCore's checked `read(address)` of `Reader`, as the literal the type checker's output is
compared with (`Contracts/Reader/Facts.lean`). -/

namespace SolidCore.Refinement.Reader

open SolidCore.Solidity.Source

/-- SolidCore's `read(address)` of `Reader`, as the checker lowers it. -/
def readFn : FunctionDef :=
{ name := "read",
  selector? := some 2693245054,
  payable := false,
  params := [{ name := "o", ty := Ty.address, isStorageRef := false }],
  paramAbiCleanups := [AbiCleanup.none],
  returns := [{ name := "_ret0", ty := Ty.uint256, isStorageRef := false }],
  body := Stmt.block
            [Stmt.skip,
             Stmt.skip,
             Stmt.block
               [Stmt.varDecl (Ty.uint256) "_sol_hoist_1" (some (Expr.word 1)),
                Stmt.varDecl (Ty.uint256) "_sol_hoist_0" none,
                Stmt.tryExternalCall
                  (SolidCore.Solidity.Shared.Call.ExternalCallKind.staticcall)
                  (Expr.var "o")
                  (Expr.encode (EncodeKind.withSelector) (some (Expr.word 2687873534)) [] [] [])
                  (Expr.word 0) none false false
                  [{ name := "__ext0", ty := Ty.uint256, isStorageRef := false }]
                  [AbiCleanup.uint 256]
                  (Stmt.assign (LValue.var "_sol_hoist_0")
                    (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "__ext0")))
                  [],
                Stmt.returnValues
                  [Expr.castOp (CastKind.uintCleanup) 256
                    (Expr.castOp (CastKind.uintCleanup) 256
                      (Expr.binary (BinaryOp.add)
                        (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "_sol_hoist_0"))
                        (Expr.castOp (CastKind.uintCleanup) 256 (Expr.var "_sol_hoist_1"))))]]],
  dispatchId? := none }

end SolidCore.Refinement.Reader
