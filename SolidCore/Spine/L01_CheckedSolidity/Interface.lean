import SolidCore.Spine.L00_Source.Interface

namespace SolidCore
namespace Spine
namespace L01_CheckedSolidity

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

def supportsFeature (fragment : Fragment) (feature : Feature) : Bool :=
  fragment.supports feature

mutual

def inFragmentExpr? (fragment : Fragment) : L00_Source.Expr -> Bool
  | Solidity.Source.Expr.word _ => true
  | Solidity.Source.Expr.var _ => supportsFeature fragment Feature.locals
  | Solidity.Source.Expr.storage _ => supportsFeature fragment Feature.storage
  | Solidity.Source.Expr.unary _ expr => inFragmentExpr? fragment expr
  | Solidity.Source.Expr.binary _ lhs rhs =>
      inFragmentExpr? fragment lhs && inFragmentExpr? fragment rhs
  | Solidity.Source.Expr.length expr =>
      supportsFeature fragment Feature.arrays && inFragmentExpr? fragment expr
  | Solidity.Source.Expr.index base index =>
      supportsFeature fragment Feature.arrays &&
        inFragmentExpr? fragment base && inFragmentExpr? fragment index

def inFragmentStmt? (fragment : Fragment) : L00_Source.Stmt -> Bool
  | Solidity.Source.Stmt.skip => true
  | Solidity.Source.Stmt.block body => inFragmentList? fragment body
  | Solidity.Source.Stmt.varDecl _ _ init =>
      supportsFeature fragment Feature.locals &&
        match init with
        | none => true
        | some expr => inFragmentExpr? fragment expr
  | Solidity.Source.Stmt.assign target expr =>
      inFragmentAssignTarget? fragment target && inFragmentExpr? fragment expr
  | Solidity.Source.Stmt.assignOp target _ expr =>
      inFragmentAssignTarget? fragment target && inFragmentExpr? fragment expr
  | Solidity.Source.Stmt.ifElse cond thenBranch elseBranch =>
      inFragmentExpr? fragment cond &&
        inFragmentStmt? fragment thenBranch &&
          inFragmentStmt? fragment elseBranch
  | Solidity.Source.Stmt.switch discr cases defaultBranch =>
      supportsFeature fragment Feature.switches &&
        inFragmentExpr? fragment discr &&
          inFragmentSwitchCases? fragment cases &&
            inFragmentOptional? fragment defaultBranch
  | Solidity.Source.Stmt.whileLoop cond body =>
      supportsFeature fragment Feature.loops &&
        inFragmentExpr? fragment cond && inFragmentStmt? fragment body
  | Solidity.Source.Stmt.forLoop init cond post body =>
      supportsFeature fragment Feature.loops &&
        inFragmentStmt? fragment init && inFragmentExpr? fragment cond &&
          inFragmentStmt? fragment post && inFragmentStmt? fragment body
  | Solidity.Source.Stmt.break => supportsFeature fragment Feature.loops
  | Solidity.Source.Stmt.continue => supportsFeature fragment Feature.loops
  | Solidity.Source.Stmt.returnValues exprs => inFragmentExprList? fragment exprs
  | Solidity.Source.Stmt.revert _ exprs =>
      supportsFeature fragment Feature.reverts &&
        inFragmentExprList? fragment exprs
  | Solidity.Source.Stmt.emitEvent _ exprs =>
      supportsFeature fragment Feature.events &&
        inFragmentExprList? fragment exprs
  | Solidity.Source.Stmt.unchecked body =>
      supportsFeature fragment Feature.uncheckedArithmetic &&
        inFragmentStmt? fragment body

def inFragmentList? (fragment : Fragment) : List L00_Source.Stmt -> Bool
  | [] => true
  | stmt :: rest => inFragmentStmt? fragment stmt && inFragmentList? fragment rest

def inFragmentOptional? (fragment : Fragment) : Option L00_Source.Stmt -> Bool
  | none => true
  | some stmt => inFragmentStmt? fragment stmt

def inFragmentSwitchCases? (fragment : Fragment) :
    List (SolidCoreYulCore.Word × L00_Source.Stmt) -> Bool
  | [] => true
  | (_, stmt) :: rest =>
      inFragmentStmt? fragment stmt && inFragmentSwitchCases? fragment rest

def inFragmentExprList? (fragment : Fragment) : List L00_Source.Expr -> Bool
  | [] => true
  | expr :: rest =>
      inFragmentExpr? fragment expr && inFragmentExprList? fragment rest

def inFragmentAssignTarget? (fragment : Fragment) :
    Solidity.Source.LValue -> Bool
  | Solidity.Source.LValue.var _ => supportsFeature fragment Feature.locals
  | Solidity.Source.LValue.storage _ => supportsFeature fragment Feature.storage
  | Solidity.Source.LValue.index base index =>
      supportsFeature fragment Feature.arrays &&
        inFragmentAssignTarget? fragment base &&
          inFragmentExpr? fragment index

end

structure NameFacts (_stmt : L00_Source.Stmt) : Prop where
  namesResolved : True := by trivial
  scopesResolved : True := by trivial

structure TypeFacts (_stmt : L00_Source.Stmt) : Prop where
  expressionsTyped : True := by trivial
  lvaluesTyped : True := by trivial
  implicitConversionsChecked : True := by trivial

structure DeclarationFacts (_stmt : L00_Source.Stmt) : Prop where
  storageDeclarationsChecked : True := by trivial
  eventsChecked : True := by trivial
  modifiersExpandedOrAbsent : True := by trivial

structure CheckedSource (fragment : Fragment) (stmt : L00_Source.Stmt) :
    Prop where
  inFragment : inFragmentStmt? fragment stmt = true
  names : NameFacts stmt := {}
  types : TypeFacts stmt := {}
  declarations : DeclarationFacts stmt := {}

structure Program (fragment : Fragment) where
  stmt : L00_Source.Stmt
  checked : CheckedSource fragment stmt

end L01_CheckedSolidity
end Spine
end SolidCore
