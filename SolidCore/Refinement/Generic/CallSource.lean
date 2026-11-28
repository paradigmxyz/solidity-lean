import SolidCore.Refinement.Generic.CallTree
import SolidCore.Refinement.Generic.SourceRun
import SolidCore.Refinement.Generic.CallNode

/-!
# SolidCore's functions with one external call, erased to call trees

`eraseFnC` erases a SolidCore function to a `CTree`: a function the call-free erasure accepts
(`eraseFn`) is a plain tree; otherwise the function of the call fragment is

* its argument checks (`paramGuardsC`, as `paramGuards`);
* then its body, whose statements before the external call, at the top of nested blocks, are
  local declarations (`localStmt`: a skip, or a word local with no initializer or a literal one),
  so that the call is the first thing the body does to the state;
* the external call (`callStmt?`): a `STATICCALL` of a target word that is not the contract itself,
  with no value, gas option or code check, whose input is a selector with no arguments, returning
  one `uint256` and with no `catch`: the call node with that request, sent with no writes;
* on success, the decoder's check (return data shorter than a word reverts with empty data), the
  returned word bound as the answer's first word `arg (n + 1)`, the success body, and the rest of
  the enclosing blocks, all call-free (`eraseStmt`, `eraseSeq`); a failure bubbles.

`CallSourceRun.source_runC` proves that SolidCore runs a call of such a function in an open world as
the call tree, with the world's answer as the callee's.
-/

namespace SolidCore.Refinement.Generic
open SolidCore.Solidity.Source SolidCore.Refinement

/-- A statement of the fragment before the external call: a skip, or a word local declared with no
initializer or a literal one. Neither reads nor changes the state. -/
def localStmt : Stmt → Bool
  | .skip => true
  | .varDecl ty _ none => wordTy ty
  | .varDecl ty _ (some (.word _)) => wordTy ty
  | _ => false

/-- The external call of the fragment: its target, the selector it calls with no arguments, the
binding of its one `uint256` result, and the success body. -/
def callStmt? : Stmt → Option (Expr × Nat × String × Stmt)
  | .tryExternalCall .staticcall tgt (.encode .withSelector (some (.word sel)) [] [] []) (.word 0) none false
      false [⟨x, .uint256, false⟩] [.uint 256] succ [] => some (tgt, sel, x, succ)
  | _ => none

/-- The input bytes of a call of the selector `sel` with no arguments. -/
def selBytes (sel : Nat) : List OByte := litBytes 4 sel

/-- The call node of an external call statement of a function with `n` parameters: its request,
and its branch tree after a successful answer. -/
def eraseCallStmt (E : EraseEnv) (n f : Nat) (s : Stmt) (S : SymState) : Option (CReq × Br) :=
  match callStmt? s with
  | none => none
  | some (tgt, sel, x, succ) =>
    if S.writes = [] ∧ S.logs = [] ∧ sel < 2 ^ 32 ∧ S.tags.get x = .word then
      match eraseExpr E.fields S tgt with
      | some ([], t) =>
        match eraseStmt E f succ { S with scopes := [(x, .arg (n + 1))] :: S.scopes } with
        | some b =>
          some (⟨true, t, .lit 0, selBytes sel⟩,
            .ite (.bin .lt (.arg n) (.lit 32)) (.leaf (.reverted .empty)) (b.mapS SymState.pop))
        | none => none
      | _ => none
    else none

/-- A statement list that reaches the external call: local declarations, then a statement with the
call, then call-free statements. -/
def eraseSeqC (fC : Stmt → SymState → Option (CReq × Br)) (fP : Stmt → SymState → Option Br) :
    List Stmt → SymState → Option (CReq × Br)
  | [], _ => none
  | s :: rest, S =>
    if localStmt s then
      match fP s S with
      | some (.leaf (.normal S')) => eraseSeqC fC fP rest S'
      | _ => none
    else
      match fC s S with
      | some (r, k) =>
        match k.bind (eraseSeq fP rest) with
        | some k' => some (r, k')
        | none => none
      | none => none

/-- A statement with the external call, at the top of nested blocks, with fuel. -/
def eraseStmtC (E : EraseEnv) (n : Nat) : Nat → Stmt → SymState → Option (CReq × Br)
  | 0, _, _ => none
  | f + 1, .block ss, S =>
    match eraseSeqC (eraseStmtC E n f) (eraseStmt E f) ss S.push with
    | some (r, k) => some (r, k.mapS SymState.pop)
    | none => none
  | f + 1, s, S => eraseCallStmt E n f s S

/-- The argument checks of a call tree, as `paramGuards`: a word of a parameter of bound
`m < 2 ^ 256 - 1` above `m` reverts with empty data, and so does a word of a signed `b`-bit
parameter (`m = wordSize + b`) that is not its own sign extension. -/
def paramGuardsC : List Nat → Nat → CTree → CTree
  | [], _, t => t
  | m :: ms, i, t =>
    if m < wordSize - 1 then
      .ite (.bin .gt (.arg i) (.lit m)) (.tree (.halt false [] [] [])) (paramGuardsC ms (i + 1) t)
    else if 0 < m - wordSize ∧ m - wordSize < 256 then
      .ite (sextGuard (m - wordSize) (.arg i)) (.tree (.halt false [] [] []))
        (paramGuardsC ms (i + 1) t)
    else paramGuardsC ms (i + 1) t

/-- **The call tree of an external call of `fn`**: the plain tree of a call-free function, or the
argument checks and the call node of a function of the call fragment. -/
def eraseFnC (E : EraseEnv) (fuel : Nat) (fn : FunctionDef) : Option CTree :=
  match eraseFn E fuel fn with
  | some t => some (.tree t)
  | none =>
    match widthsOf fn.params fn.paramAbiCleanups with
    | none => none
    | some ws =>
      if fn.returns.all wordBinding then
        match eraseStmtC { E with facts := argFacts ws 0 } fn.params.length fuel fn.body (initState fn) with
        | some (r, k) =>
          match brTree fn (argFacts ws 0) k with
          | some t => some (paramGuardsC ws 0 (.call r [] fn.params.length t))
          | none => none
        | none => none
      else none

end SolidCore.Refinement.Generic

