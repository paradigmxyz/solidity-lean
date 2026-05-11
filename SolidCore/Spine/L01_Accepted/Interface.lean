import SolidCore.Spine.L00_Source.Interface

namespace SolidCore
namespace Spine
namespace L01_Accepted

inductive Feature where
  | locals
  | storage
  | arrays
  | events
  | reverts
  | switches
  | loops
  | uncheckedArithmetic
  deriving DecidableEq, Repr

structure Fragment where
  supports : Feature -> Bool := fun _ => false

def Fragment.all : Fragment where
  supports := fun _ => true

def Fragment.basicControl : Fragment where
  supports
    | Feature.locals => true
    | Feature.reverts => true
    | Feature.switches => true
    | Feature.uncheckedArithmetic => true
    | _ => false

def acceptsFeature (fragment : Fragment) (feature : Feature) : Bool :=
  fragment.supports feature

mutual

def acceptedExpr? (fragment : Fragment) : L00_Source.Expr -> Bool
  | Solidity.Source.Expr.word _ => true
  | Solidity.Source.Expr.var _ => acceptsFeature fragment Feature.locals
  | Solidity.Source.Expr.storage _ => acceptsFeature fragment Feature.storage
  | Solidity.Source.Expr.unary _ expr => acceptedExpr? fragment expr
  | Solidity.Source.Expr.binary _ lhs rhs =>
      acceptedExpr? fragment lhs && acceptedExpr? fragment rhs
  | Solidity.Source.Expr.length expr =>
      acceptsFeature fragment Feature.arrays && acceptedExpr? fragment expr
  | Solidity.Source.Expr.index base index =>
      acceptsFeature fragment Feature.arrays &&
        acceptedExpr? fragment base && acceptedExpr? fragment index

def acceptedStmt? (fragment : Fragment) : L00_Source.Stmt -> Bool
  | Solidity.Source.Stmt.skip => true
  | Solidity.Source.Stmt.block body => acceptedList? fragment body
  | Solidity.Source.Stmt.varDecl _ _ init =>
      acceptsFeature fragment Feature.locals &&
        match init with
        | none => true
        | some expr => acceptedExpr? fragment expr
  | Solidity.Source.Stmt.assign target expr =>
      acceptedAssignTarget? fragment target && acceptedExpr? fragment expr
  | Solidity.Source.Stmt.assignOp target _ expr =>
      acceptedAssignTarget? fragment target && acceptedExpr? fragment expr
  | Solidity.Source.Stmt.ifElse cond thenBranch elseBranch =>
      acceptedExpr? fragment cond &&
        acceptedStmt? fragment thenBranch &&
          acceptedStmt? fragment elseBranch
  | Solidity.Source.Stmt.switch discr cases defaultBranch =>
      acceptsFeature fragment Feature.switches &&
        acceptedExpr? fragment discr &&
          acceptedSwitchCases? fragment cases &&
            acceptedOptional? fragment defaultBranch
  | Solidity.Source.Stmt.whileLoop cond body =>
      acceptsFeature fragment Feature.loops &&
        acceptedExpr? fragment cond && acceptedStmt? fragment body
  | Solidity.Source.Stmt.forLoop init cond post body =>
      acceptsFeature fragment Feature.loops &&
        acceptedStmt? fragment init && acceptedExpr? fragment cond &&
          acceptedStmt? fragment post && acceptedStmt? fragment body
  | Solidity.Source.Stmt.break => acceptsFeature fragment Feature.loops
  | Solidity.Source.Stmt.continue => acceptsFeature fragment Feature.loops
  | Solidity.Source.Stmt.returnValues exprs => acceptedExprList? fragment exprs
  | Solidity.Source.Stmt.revert _ exprs =>
      acceptsFeature fragment Feature.reverts &&
        acceptedExprList? fragment exprs
  | Solidity.Source.Stmt.emitEvent _ exprs =>
      acceptsFeature fragment Feature.events &&
        acceptedExprList? fragment exprs
  | Solidity.Source.Stmt.unchecked body =>
      acceptsFeature fragment Feature.uncheckedArithmetic &&
        acceptedStmt? fragment body

def acceptedList? (fragment : Fragment) : List L00_Source.Stmt -> Bool
  | [] => true
  | stmt :: rest => acceptedStmt? fragment stmt && acceptedList? fragment rest

def acceptedOptional? (fragment : Fragment) : Option L00_Source.Stmt -> Bool
  | none => true
  | some stmt => acceptedStmt? fragment stmt

def acceptedSwitchCases? (fragment : Fragment) :
    List (SolidCoreYulCore.Word × L00_Source.Stmt) -> Bool
  | [] => true
  | (_, stmt) :: rest =>
      acceptedStmt? fragment stmt && acceptedSwitchCases? fragment rest

def acceptedExprList? (fragment : Fragment) : List L00_Source.Expr -> Bool
  | [] => true
  | expr :: rest =>
      acceptedExpr? fragment expr && acceptedExprList? fragment rest

def acceptedAssignTarget? (fragment : Fragment) :
    Solidity.Source.LValue -> Bool
  | Solidity.Source.LValue.var _ => acceptsFeature fragment Feature.locals
  | Solidity.Source.LValue.storage _ => acceptsFeature fragment Feature.storage
  | Solidity.Source.LValue.index base index =>
      acceptsFeature fragment Feature.arrays &&
        acceptedAssignTarget? fragment base &&
          acceptedExpr? fragment index

end

structure AcceptedSource (fragment : Fragment) (stmt : L00_Source.Stmt) :
    Prop where
  accepted : acceptedStmt? fragment stmt = true

end L01_Accepted
end Spine
end SolidCore
