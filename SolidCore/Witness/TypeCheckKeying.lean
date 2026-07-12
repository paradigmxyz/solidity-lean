import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
R4 — SOURCE-KEYED CONVERSION PREDICATES + PER-RECEIVER MEMBER TABLE.

Pins a broad sample of the conversion matrix (accepts AND rejects) across
every source-type family after the R4 rearchitecture of
`Ty.canExplicitlyConvert` / `Ty.canImplicitlyConvert` /
`TypeContext.canImplicitlyConvert(Fuel)` into solc's per-source-type
dispatch shape (Types.h:224-227), plus the builtin member tables
(`Ty.builtinValueMembers` / `TypeContext.builtinMetaMembers`, mirroring
solc `Type::members()`), plus the ONE genuine fix of the phase:

  TARGET-4 FIX (pinned-solc-verified over-reject): `TypeContext.
  commonImplicit?` routes the common-type fallback through the
  context-AWARE implicit convertibility (solc `Type::commonType`,
  Types.cpp:279-295), so an inline array literal of related contract
  values deduces its common base:
      Base[2] memory arr = [derived, base];   // solc 0.8.35 ACCEPTS
  was rejected before R4 ("array literal common type"), and is accepted
  now (imported AST `probe2` below). The reject neighbor with UNRELATED
  contracts stays rejected — pinned solc: "Unable to deduce common type
  for array elements" (probe3, hand-built: solc emits no AST for it).

Everything else in this phase is a behavior-preserving structural rewrite:
the R4 differential matrix (scratchpad audit-r4/Matrix.lean, 18095 verdict
lines over a 55-type grid, literal sources, and 55×23 member grids) is
IDENTICAL before/after every target commit.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace TypeCheckKeying

open SolidCore.Solidity.TypeCheck

private def p (n : String) : Path := { segments := [n] }

private def receiveFn : FunctionDecl :=
  { kind := FunctionKind.receive
    name := none
    params := []
    returns := []
    visibility := some Visibility.external_
    mutability := StateMutability.payable
    body := some (Stmt.block []) }

/-- C receives ether; N does not; D derives from C; L library; I interface;
    enums E/E2; UDVTs U/U8; struct S. -/
private def ctx : TypeContext :=
  { contracts := [p "C", p "N", p "D", p "L", p "I"]
    contractDecls :=
      [(p "C", { name := "C", items := [ContractItem.function receiveFn] }),
        (p "N", { name := "N" }),
        (p "D", { name := "D", bases := [{ base := p "C" }] }),
        (p "L", { name := "L", kind := ContractKind.library }),
        (p "I", { name := "I", kind := ContractKind.interface })]
    structs := [(p "S", { name := "S", fields := [{ name := "a", ty := Ty.uint 256 }] })]
    -- NOTE: an entry list places importer ALIAS pairs adjacently
    -- (`pathsAreLocalAliasIn` treats (short, qualified) NEIGHBORS as the
    -- same declaration), so keep E and E2 non-adjacent here.
    enums := [(p "E", { name := "E", cases := ["A", "B", "Cc"] }),
              (p "EM", { name := "EM", cases := ["M0"] }),
              (p "E2", { name := "E2", cases := ["X"] })]
    userValueTypes := [(p "U", Ty.uint 256), (p "U8", Ty.uint 8)] }

private def x : Expr := Expr.ident "x"

private def expl (a b : Ty) : Bool := Ty.canExplicitlyConvert ctx x a b
private def impl (a b : Ty) : Bool := Ty.canImplicitlyConvert a b
private def cimpl (a b : Ty) : Bool := TypeContext.canImplicitlyConvert ctx a b
private def saca (dest src : Ty) : Bool := Ty.storageArrayCopyAssignable? ctx dest src

-- ===========================================================================
-- EXPLICIT conversions (typed, non-literal source) — source-keyed dispatch.
-- ===========================================================================

-- address sources (AddressType::isExplicitlyConvertibleTo, Types.cpp:495-510)
#guard expl (Ty.address true) (Ty.address false)          -- payable → address
#guard !(expl (Ty.address false) (Ty.address true))       -- no explicit → payable
#guard expl (Ty.address false) (Ty.uint 160)              -- non-payable → uint160
#guard !(expl (Ty.address true) (Ty.uint 160))            -- payable → uint160 REJECT
#guard expl (Ty.address false) (Ty.bytesN 20)
#guard !(expl (Ty.address true) (Ty.bytesN 20))
#guard !(expl (Ty.address false) (Ty.uint 256))
#guard expl (Ty.address true) (Ty.user (p "C"))           -- payable → receiving contract
#guard !(expl (Ty.address false) (Ty.user (p "C")))       -- non-payable → receiving REJECT
#guard expl (Ty.address false) (Ty.user (p "N"))          -- non-receiving contract OK
#guard !(expl (Ty.address false) (Ty.user (p "E")))       -- address → enum REJECT

-- integer sources (IntegerType::isExplicitlyConvertibleTo, Types.cpp:627-646)
#guard expl (Ty.uint 160) (Ty.address false)
#guard !(expl (Ty.uint 8) (Ty.address false))
#guard !(expl (Ty.int 160) (Ty.address false))            -- signed → address REJECT
#guard expl (Ty.uint 256) (Ty.uint 8)                     -- explicit narrowing
#guard expl (Ty.uint 256) (Ty.int 256)                    -- same width, cross sign
#guard !(expl (Ty.uint 256) (Ty.int 128))                 -- diff width + cross sign
#guard expl (Ty.int 8) (Ty.int 256)
#guard expl (Ty.uint 256) (Ty.bytesN 32)                  -- unsigned, same total width
#guard expl (Ty.uint 32) (Ty.fixedBytes 4)
#guard !(expl (Ty.uint 8) (Ty.bytesN 4))                  -- width mismatch
#guard !(expl (Ty.int 256) (Ty.bytesN 32))                -- signed → bytesN REJECT (A3)
#guard expl (Ty.uint 8) (Ty.user (p "E"))                 -- integer → enum
#guard expl (Ty.int 8) (Ty.user (p "E"))                  -- signed integer → enum too
#guard !(expl (Ty.uint 8) (Ty.user (p "U")))              -- integer → UDVT REJECT

-- fixed-bytes sources (FixedBytesType::isExplicitlyConvertibleTo, 1360-1377)
#guard expl (Ty.bytesN 20) (Ty.address false)
#guard expl (Ty.fixedBytes 20) (Ty.address false)
#guard !(expl (Ty.bytesN 32) (Ty.address false))
#guard expl (Ty.bytesN 32) (Ty.uint 256)
#guard expl (Ty.fixedBytes 4) (Ty.uint 32)
#guard !(expl (Ty.bytesN 32) (Ty.int 256))                -- → signed REJECT
#guard expl (Ty.bytesN 32) (Ty.bytesN 4)                  -- truncation OK
#guard expl (Ty.bytesN 4) (Ty.fixedBytes 32)              -- widening OK (cross spelling)
#guard !(expl (Ty.bytesN 32) (Ty.user (p "E")))           -- bytes32 → enum REJECT

-- byte-array sources (ArrayType::isExplicitlyConvertibleTo, 1668-1680)
#guard expl Ty.bytes Ty.string
#guard expl Ty.string Ty.bytes
#guard expl Ty.bytes (Ty.bytesN 4)                        -- bytes → bytesNN
#guard !(expl Ty.string (Ty.bytesN 4))                    -- typed string → bytesN REJECT
#guard !(expl Ty.bytes (Ty.uint 256))

-- user sources (ContractType 1491-1499 / EnumType 2674-2681 / base default)
#guard expl (Ty.user (p "C")) (Ty.address false)          -- contract → address
#guard expl (Ty.user (p "D")) (Ty.user (p "C"))           -- UP-cast
#guard !(expl (Ty.user (p "C")) (Ty.user (p "D")))        -- down-cast REJECT (A4)
#guard expl (Ty.user (p "E")) (Ty.uint 8)                 -- enum → any unsigned width
#guard expl (Ty.user (p "E")) (Ty.uint 256)
#guard !(expl (Ty.user (p "E")) (Ty.int 256))             -- enum → signed REJECT
#guard !(expl (Ty.user (p "E")) (Ty.user (p "E2")))       -- enum → other enum REJECT
#guard !(expl (Ty.user (p "U")) (Ty.uint 256))            -- UDVT → underlying REJECT
#guard !(expl (Ty.user (p "S")) (Ty.uint 256))            -- struct path → REJECT

-- default-only sources (base Type::isExplicitlyConvertibleTo)
#guard !(expl Ty.bool (Ty.uint 8))
#guard !(expl (Ty.uint 8) Ty.bool)
#guard !(expl (Ty.array (Ty.uint 8) none) (Ty.array (Ty.uint 256) none))
#guard !(expl (Ty.mapping (Ty.uint 256) (Ty.uint 256)) (Ty.uint 256))

-- untyped-literal layer (RationalNumberType, Types.cpp:1042-1064)
private def lit (s : String) : Expr := Expr.literal (Literal.number s)
#guard Ty.canExplicitlyConvert ctx (lit "1") (Ty.uint 256) (Ty.uint 8)
#guard !(Ty.canExplicitlyConvert ctx (lit "300") (Ty.uint 256) (Ty.uint 8))
#guard Ty.canExplicitlyConvert ctx (lit "2") (Ty.uint 256) (Ty.user (p "E"))
#guard !(Ty.canExplicitlyConvert ctx (lit "3") (Ty.uint 256) (Ty.user (p "E")))
#guard Ty.canExplicitlyConvert ctx
  (lit "0x00000000219ab540356cBB839Cbe05303d7705Fa")
  (Ty.uint 256) (Ty.address false)
#guard !(Ty.canExplicitlyConvert ctx (lit "1") (Ty.uint 256) Ty.bool)

-- ===========================================================================
-- IMPLICIT conversions — source-keyed core + context rules.
-- ===========================================================================
#guard impl (Ty.uint 8) (Ty.uint 256)
#guard !(impl (Ty.uint 256) (Ty.uint 8))
#guard !(impl (Ty.uint 8) (Ty.int 16))                    -- A1: cross-sign REJECT
#guard !(impl (Ty.int 8) (Ty.uint 256))
#guard impl (Ty.int 8) (Ty.int 256)
#guard impl (Ty.bytesN 4) (Ty.bytesN 32)
#guard impl (Ty.bytesN 4) (Ty.fixedBytes 32)
#guard impl (Ty.fixedBytes 4) (Ty.bytesN 32)
#guard !(impl (Ty.bytesN 32) (Ty.bytesN 4))
#guard impl (Ty.address true) (Ty.address false)
#guard !(impl (Ty.address false) (Ty.address true))
#guard !(impl (Ty.user (p "D")) (Ty.user (p "C")))        -- context-free: no covariance
#guard impl (Ty.user (p "E")) (Ty.user (p "E"))           -- identity
#guard !(impl Ty.bytes Ty.string)

#guard cimpl (Ty.user (p "D")) (Ty.user (p "C"))          -- covariance (context)
#guard !(cimpl (Ty.user (p "C")) (Ty.user (p "D")))
#guard !(cimpl (Ty.user (p "E")) (Ty.user (p "E2")))
#guard !(cimpl (Ty.user (p "E")) (Ty.uint 256))
#guard cimpl (Ty.uint 8) (Ty.uint 256)                    -- core still reachable
#guard !(cimpl (Ty.array (Ty.uint 8) none) (Ty.array (Ty.uint 256) none))
  -- ordinary (non-storage-copy) context: arrays are identity-only
#guard cimpl (Ty.array (Ty.uint 8) none) (Ty.array (Ty.uint 8) none)

-- storage-copy relaxation (ArrayType::isImplicitlyConvertibleTo, 1640-1648)
#guard saca (Ty.array (Ty.uint 256) none) (Ty.array (Ty.uint 8) (some 2))
#guard saca (Ty.array (Ty.uint 8) (some 3)) (Ty.array (Ty.uint 8) (some 2))
#guard !(saca (Ty.array (Ty.uint 8) (some 2)) (Ty.array (Ty.uint 8) (some 3)))
#guard !(saca (Ty.array (Ty.uint 8) (some 2)) (Ty.array (Ty.uint 8) none))
#guard saca (Ty.array (Ty.array (Ty.uint 8) (some 3)) (some 3))
  (Ty.array (Ty.array (Ty.uint 8) (some 2)) (some 2))
#guard saca (Ty.array (Ty.user (p "C")) none) (Ty.array (Ty.user (p "D")) none)
  -- element covariance through the storage copy
#guard !(saca (Ty.array (Ty.user (p "S")) none) (Ty.array (Ty.user (p "S")) none))
  -- legacy-codegen direct-struct-element carve-out (task #122)

-- ===========================================================================
-- BUILTIN MEMBER TABLES (solc Type::members shape).
-- ===========================================================================
#guard (Ty.builtinValueMemberInfo? (Ty.address false) "balance").map
  (fun i => i.ty) == some (Ty.uint 256)
#guard (Ty.builtinValueMemberInfo? (Ty.address true) "code").map
  (fun i => i.ty) == some Ty.bytes
#guard (Ty.builtinValueMemberInfo? (Ty.address false) "codehash").map
  (fun i => i.needsConstantinople) == some true
#guard (Ty.builtinValueMemberInfo? (Ty.address false) "balance").map
  (fun i => i.needsStateRead) == some true
#guard (Ty.builtinValueMemberInfo? Ty.bytes "length").map
  (fun i => i.ty) == some (Ty.uint 256)
#guard (Ty.builtinValueMemberInfo? (Ty.array (Ty.uint 8) (some 2)) "length").map
  (fun i => i.needsStateRead) == some false
#guard (Ty.builtinValueMemberInfo? (Ty.bytesN 4) "length").isSome
#guard (Ty.builtinValueMemberInfo? (Ty.uint 256) "balance").isNone
#guard (Ty.builtinValueMemberInfo? Ty.string "length").isNone -- string: NO length
#guard (Ty.builtinValueMemberInfo? (Ty.address false) "length").isNone
#guard (Ty.builtinValueMemberInfo? Ty.bytes "balance").isNone

#guard TypeContext.builtinMetaMemberTy? ctx (Ty.uint 8) "max" == some (Ty.uint 8)
#guard TypeContext.builtinMetaMemberTy? ctx (Ty.int 256) "min" == some (Ty.int 256)
#guard (TypeContext.builtinMetaMemberTy? ctx (Ty.uint 8) "name").isNone
#guard TypeContext.builtinMetaMemberTy? ctx (Ty.user (p "E")) "min"
  == some (Ty.user (p "E"))
#guard TypeContext.builtinMetaMemberTy? ctx (Ty.user (p "E")) "B"
  == some (Ty.user (p "E"))
#guard (TypeContext.builtinMetaMemberTy? ctx (Ty.user (p "E")) "Z").isNone
#guard TypeContext.builtinMetaMemberTy? ctx (Ty.user (p "C")) "name"
  == some Ty.string
#guard TypeContext.builtinMetaMemberTy? ctx (Ty.user (p "C")) "creationCode"
  == some Ty.bytes
#guard TypeContext.builtinMetaMemberTy? ctx (Ty.user (p "C")) "interfaceId"
  == some (Ty.bytesN 4)
#guard (TypeContext.builtinMetaMemberTy? ctx (Ty.user (p "C")) "min").isNone
#guard (TypeContext.builtinMetaMemberTy? ctx (Ty.user (p "S")) "max").isNone

-- End-to-end: value members through `checkExpr` (whole-unit acceptance).
private def ret (e : Expr) : Stmt := Stmt.returnValues (some e)

private def memberFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "m"
    visibility := some Visibility.public_
    mutability := StateMutability.view
    params :=
      [{ name := some "a", ty := Ty.address false, location := none },
        { name := some "bs", ty := Ty.bytes, location := some DataLocation.memory }]
    returns := [{ name := none, ty := Ty.uint 256, location := none }]
    body := some (Stmt.block
      [Stmt.varDecl
          [{ name := some "h", ty := Ty.bytesN 32, location := none }]
          (some (Expr.member (Expr.ident "a") "codehash")),
        ret (Expr.binary BinaryOp.add
          (Expr.binary BinaryOp.add
            (Expr.member (Expr.ident "a") "balance")
            (Expr.member (Expr.ident "bs") "length"))
          (Expr.member (Expr.typeName (Ty.uint 256)) "max"))]) }

private def memberSourceUnit : SourceUnit :=
  { items :=
      [SourceItem.pragma "solidity" "^0.8.35",
        SourceItem.contract { name := "M", items := [ContractItem.function memberFn] }] }

def memberProgramAccepted : Bool :=
  Result.isOk (TypecheckedInput.checkedSourceUnit memberSourceUnit)

#guard memberProgramAccepted

-- Reserved builtin name on the WRONG receiver must reject (no fallback leak).
private def badBalanceFn : FunctionDecl :=
  { memberFn with
    params := [{ name := some "a", ty := Ty.uint 256, location := none }]
    body := some (Stmt.block [ret (Expr.member (Expr.ident "a") "balance")]) }

private def badBalanceContract : ContractDecl :=
  { name := "M", items := [ContractItem.function badBalanceFn] }

private def badBalanceSourceUnit : SourceUnit :=
  { items :=
      [SourceItem.pragma "solidity" "^0.8.35",
        SourceItem.contract badBalanceContract] }

def badBalanceRejected : Bool :=
  Result.isError (TypecheckedInput.checkedSourceUnit badBalanceSourceUnit)

#guard badBalanceRejected

-- ===========================================================================
-- TARGET-4 FIX: context-aware common type (solc Type::commonType).
-- ===========================================================================
#guard TypeContext.commonImplicit? ctx (Ty.user (p "D")) (Ty.user (p "C"))
  == some (Ty.user (p "C"))
#guard TypeContext.commonImplicit? ctx (Ty.user (p "C")) (Ty.user (p "D"))
  == some (Ty.user (p "C"))
#guard (TypeContext.commonImplicit? ctx (Ty.user (p "C")) (Ty.user (p "N"))).isNone
#guard (TypeContext.commonImplicit? ctx (Ty.user (p "E")) (Ty.user (p "E2"))).isNone
#guard (Ty.commonImplicit? (Ty.user (p "D")) (Ty.user (p "C"))).isNone
  -- the context-FREE table alone still deduces nothing for user pairs
#guard TypeContext.commonImplicit? ctx (Ty.uint 8) (Ty.uint 16)
  == some (Ty.uint 16)

end TypeCheckKeying
end Witness
end Solidity
end SolidCore

-- ===========================================================================
-- Imported AST (pinned solc 0.8.35 --contract P, probe2.sol): solc ACCEPTS
--   Base[2] memory arr = [d, b];   // d : Derived is Base, b : Base
-- Model must accept too (was the pre-R4 over-reject).
-- ===========================================================================
namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TypeCheckKeyingProbe2

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Base"
  abstract := false
  bases := []
  items := [] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Derived"
  abstract := false
  bases := [{ base := { segments := ["Base"] }, args := [] }]
  items := [] }

def importedContractDecl2 : ContractDecl :=
{ kind := ContractKind.contract
  name := "P"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [{ name := some "d", ty := Ty.user ({ segments := ["Derived"] }), location := none }, { name := some "b", ty := Ty.user ({ segments := ["Base"] }), location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.user ({ segments := ["Base"] })) (some 2), location := some DataLocation.memory }] (some (Expr.array [Expr.ident "d", Expr.ident "b"])), Stmt.returnValues (some (Expr.member (Expr.ident "arr") "length"))]) })] }

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1, SourceItem.contract importedContractDecl2] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

#guard importedContractAccepted

-- Reject neighbor (hand-built; solc REJECTS probe3.sol with "Unable to
-- deduce common type for array elements", so it has no importable AST):
-- `[b, o]` with UNRELATED contracts Base / Other.
def unrelatedDecl : ContractDecl :=
{ kind := ContractKind.contract
  name := "Other"
  abstract := false
  bases := []
  items := [] }

def unrelatedP : ContractDecl :=
{ kind := ContractKind.contract
  name := "P"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [{ name := some "b", ty := Ty.user ({ segments := ["Base"] }), location := none }, { name := some "o", ty := Ty.user ({ segments := ["Other"] }), location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.user ({ segments := ["Base"] })) (some 2), location := some DataLocation.memory }] (some (Expr.array [Expr.ident "b", Expr.ident "o"])), Stmt.returnValues (some (Expr.member (Expr.ident "arr") "length"))]) })] }

def unrelatedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
      SourceItem.contract importedContractDecl0,
      SourceItem.contract unrelatedDecl,
      SourceItem.contract unrelatedP] }

def unrelatedRejected : Bool :=
  TypeCheck.Result.isError
    (TypeCheck.TypecheckedInput.checkedSourceUnit unrelatedSourceUnit)

#guard unrelatedRejected

end TypeCheckKeyingProbe2
end SolcAstImport
end Solidity
end SolidCore
