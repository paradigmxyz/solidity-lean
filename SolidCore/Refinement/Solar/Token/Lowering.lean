import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.KernelCopies
import SolidCore.Refinement.KernelRfl
import SolidCore.Refinement.Source.Token
import token.gen.Token.Stage0

/-!
# token: the generic source stage on an ERC-20-like token

scripts/refinement/token/token.sol,

    contract Token {
      mapping(address => uint256) balances;
      mapping(address => mapping(address => uint256)) allowances;
      mapping(address => bool) frozen;
      uint256 totalSupply; address owner;
      event Transfer(address indexed from, address indexed to, uint256 value);
      event Approval(address indexed owner, address indexed spender, uint256 value);
      function balanceOf(address who) external view returns (uint256);
      function allowance(address holder, address spender) external view returns (uint256);
      function getOwner() external view returns (address);
      function isFrozen(address who) external view returns (bool);
      function freeze(address who) external;               // require(msg.sender == owner)
      function transfer(address to, uint256 value) external returns (bool);
      function approve(address spender, uint256 value) external returns (bool);
      function transferFrom(address from, address to, uint256 value) external returns (bool); }

has a nested mapping (an allowance at `keccak256(spender, keccak256(holder, 1))`), a mapping to
`bool` (read as the low byte of its word not zero), an `address` field (`owner`, slot 4), view
functions returning a `uint256`, an `address` and a `bool`, `require(c)` (empty revert data),
`require(c, "balance")` and `revert("allowance")` (`Error(string)` revert data), an
`if`/`else if` on a `uint256` local against `type(uint256).max`, and logs with two indexed
address topics taken from `msg.sender` and from parameters.

`SolarTV.Export.Token.stage0` is solar's first lowered MIR module for it after
`lower-evm-shaped`: solar's own `-Zemit-lean-stages` export (solar 0.8.38+commit.3ca8f483,
-Zcheck-analyses=false -Ogas, osaka; sha256 ee5ac4da…3dae) in solar's solar-tv/milestone/token,
imported from there: the one definition both this source stage and solar-tv's backend stages
(`SolarTV.Milestone.Token.token_mir_to_evmir`) are about, so the stages compose.

SolidCore's core (`coreLit`, solc 0.8.35's AST through scripts/solc_ast_to_lean_source.py into
Source/Token.lean and `TypeCheck.CheckedInput.contract`, printed and copied) is erased by
`Generic.eraseFn`; the module is run symbolically with the environment flag
(`Generic.symTree … .all`): the caller is `callerWord`, a mapping slot the word
`hash key slot`. Both trees agree in canonical form for every function.

* `shape_eq`: `Token` type checks, its core is `coreLit`, its constructor leaves no storage;
* `check_stage0`, `checkValue_stage0`: the generic check accepts stage0 for the eight
  external functions, at no value and at any value (`decide +kernel`);
* `check_rejects_map2`, `check_rejects_frozen`, `check_rejects_approval`: it rejects stage0
  with `allowance`'s two keys hashed in the other order, with `transfer`'s `frozen` check
  dropped, and with `approve`'s `Approval` topic changed;
* `lowering`, `loweringValue`: the stage from SolidCore to stage0 on every call of the eight
  functions, from any storage, under every oracle with SolidCore's caller and hash of two words
  (`Generic.SourceEnvOk`).

No sorry, native_decide or bv_decide.
-/

namespace SolidCore.Refinement.Solar.Token

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity SolidCore.Solidity.Source
open SolarTV.Export.Token (stage0)

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- The interpreter fuel of the symbolic run of the module: steps along each path. -/
def mirFuel : Nat := 40

/-- SolidCore's checked `Token`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.Token.importedSourceUnit "Token"

/-- The selector of `balanceOf(address)`. -/
abbrev balanceOfSel : Nat := 0x70a08231

/-- The selector of `allowance(address,address)`. -/
abbrev allowanceSel : Nat := 0xdd62ed3e

/-- The selector of `getOwner()`. -/
abbrev getOwnerSel : Nat := 0x893d20e8

/-- The selector of `isFrozen(address)`. -/
abbrev isFrozenSel : Nat := 0xe5839836

/-- The selector of `freeze(address)`. -/
abbrev freezeSel : Nat := 0x8d1fdf2f

/-- The selector of `transfer(address,uint256)`. -/
abbrev transferSel : Nat := 0xa9059cbb

/-- The selector of `approve(address,uint256)`. -/
abbrev approveSel : Nat := 0x095ea7b3

/-- The selector of `transferFrom(address,address,uint256)`. -/
abbrev transferFromSel : Nat := 0x23b872dd

/-- `balanceOf` and its parameters (an address is a word of 160 bits). -/
def fnBalanceOf : Fn := ⟨balanceOfSel, [.uint 160]⟩

/-- `allowance` and its parameters (an address is a word of 160 bits). -/
def fnAllowance : Fn := ⟨allowanceSel, [.uint 160, .uint 160]⟩

/-- `getOwner` and its parameters (an address is a word of 160 bits). -/
def fnGetOwner : Fn := ⟨getOwnerSel, []⟩

/-- `isFrozen` and its parameters (an address is a word of 160 bits). -/
def fnIsFrozen : Fn := ⟨isFrozenSel, [.uint 160]⟩

/-- `freeze` and its parameters (an address is a word of 160 bits). -/
def fnFreeze : Fn := ⟨freezeSel, [.uint 160]⟩

/-- `transfer` and its parameters (an address is a word of 160 bits). -/
def fnTransfer : Fn := ⟨transferSel, [.uint 160, .uint 256]⟩

/-- `approve` and its parameters (an address is a word of 160 bits). -/
def fnApprove : Fn := ⟨approveSel, [.uint 160, .uint 256]⟩

/-- `transferFrom` and its parameters (an address is a word of 160 bits). -/
def fnTransferFrom : Fn := ⟨transferFromSel, [.uint 160, .uint 160, .uint 256]⟩

/-- The external functions of `Token`. -/
def fns : List Fn :=
  [fnBalanceOf, fnAllowance, fnGetOwner, fnIsFrozen, fnFreeze, fnTransfer, fnApprove, fnTransferFrom]

/-- SolidCore's core contract of `Token`, as the type checker leaves it. -/
def coreLit : Contract :=
  { storageFields := [{ name := "balances",
                        slot := 0,
                        ty? := none,
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.mapping
                                     (SolidCore.Solidity.Source.Ty.address)
                                     (SolidCore.Solidity.Source.StorageLayout.scalar
                                       (SolidCore.Solidity.Source.Ty.uint256))),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 32,
                        packedSigned := false },
                      { name := "allowances",
                        slot := 1,
                        ty? := none,
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.mapping
                                     (SolidCore.Solidity.Source.Ty.address)
                                     (SolidCore.Solidity.Source.StorageLayout.mapping
                                       (SolidCore.Solidity.Source.Ty.address)
                                       (SolidCore.Solidity.Source.StorageLayout.scalar
                                         (SolidCore.Solidity.Source.Ty.uint256)))),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 32,
                        packedSigned := false },
                      { name := "frozen",
                        slot := 2,
                        ty? := none,
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.mapping
                                     (SolidCore.Solidity.Source.Ty.address)
                                     (SolidCore.Solidity.Source.StorageLayout.scalar
                                       (SolidCore.Solidity.Source.Ty.bool))),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 32,
                        packedSigned := false },
                      { name := "totalSupply",
                        slot := 3,
                        ty? := some (SolidCore.Solidity.Source.Ty.uint256),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.uint256)),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 32,
                        packedSigned := false },
                      { name := "owner",
                        slot := 4,
                        ty? := some (SolidCore.Solidity.Source.Ty.address),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.address)),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 20,
                        packedSigned := false }],
    immutableFields := [],
    eventDecls := [{ name := "Transfer",
                     indexedCount := 2,
                     topic? := some 100389287136786176327247604509743168900146139575972864366142685224231313322991,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false }] },
                   { name := "Approval",
                     indexedCount := 2,
                     topic? := some 63486140976153616755203102783360879283472101686154884697241723088393386309925,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false }] },
                   { name := "Token.Transfer",
                     indexedCount := 2,
                     topic? := some 100389287136786176327247604509743168900146139575972864366142685224231313322991,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false }] },
                   { name := "Token.Approval",
                     indexedCount := 2,
                     topic? := some 63486140976153616755203102783360879283472101686154884697241723088393386309925,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false }] }],
    errorDecls := [],
    functions := [{ name := "balanceOf",
                    selector? := some 1889567281,
                    payable := false,
                    params := [{ name := "who", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.element)
                                         "balances"
                                         [SolidCore.Solidity.Source.Expr.var "who"])]]],
                    dispatchId? := none },
                  { name := "allowance",
                    selector? := some 3714247998,
                    payable := false,
                    params := [{ name := "holder", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "spender", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.index
                                         (SolidCore.Solidity.Source.Expr.storageRead
                                           (SolidCore.Solidity.Source.StorageReadMode.element)
                                           "allowances"
                                           [SolidCore.Solidity.Source.Expr.var "holder"])
                                         (SolidCore.Solidity.Source.Expr.var "spender"))]]],
                    dispatchId? := none },
                  { name := "getOwner",
                    selector? := some 2302484712,
                    payable := false,
                    params := [],
                    paramAbiCleanups := [],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.storageRead
                                       (SolidCore.Solidity.Source.StorageReadMode.ref)
                                       "owner"
                                       []]]],
                    dispatchId? := none },
                  { name := "isFrozen",
                    selector? := some 3850606646,
                    payable := false,
                    params := [{ name := "who", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.bool, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.storageRead
                                       (SolidCore.Solidity.Source.StorageReadMode.element)
                                       "frozen"
                                       [SolidCore.Solidity.Source.Expr.var "who"]]]],
                    dispatchId? := none },
                  { name := "freeze",
                    selector? := some 2367676207,
                    payable := false,
                    params := [{ name := "who", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.requireStmt
                                    (SolidCore.Solidity.Source.Expr.binary
                                      (SolidCore.Solidity.Source.BinaryOp.eq)
                                      (SolidCore.Solidity.Source.Expr.caller)
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.ref)
                                        "owner"
                                        []))
                                    none,
                                  SolidCore.Solidity.Source.Stmt.assign
                                    (SolidCore.Solidity.Source.LValue.storageIndex
                                      "frozen"
                                      (SolidCore.Solidity.Source.Expr.var "who"))
                                    (SolidCore.Solidity.Source.Expr.word 1)]],
                    dispatchId? := none },
                  { name := "transfer",
                    selector? := some 2835717307,
                    payable := false,
                    params := [{ name := "to", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "value", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.bool, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "value")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "value")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.requireStmt
                                    (SolidCore.Solidity.Source.Expr.unary
                                      (SolidCore.Solidity.Source.UnaryOp.logicalNot)
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "frozen"
                                        [SolidCore.Solidity.Source.Expr.caller]))
                                    none,
                                  SolidCore.Solidity.Source.Stmt.requireStmt
                                    (SolidCore.Solidity.Source.Expr.binary
                                      (SolidCore.Solidity.Source.BinaryOp.ge)
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.storageRead
                                          (SolidCore.Solidity.Source.StorageReadMode.element)
                                          "balances"
                                          [SolidCore.Solidity.Source.Expr.caller]))
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.var "value")))
                                    (some "balance"),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.sub))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "balances"
                                        [SolidCore.Solidity.Source.Expr.caller])
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "balances"
                                        [SolidCore.Solidity.Source.Expr.var "to"])
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Transfer"
                                    [SolidCore.Solidity.Source.Expr.caller,
                                     SolidCore.Solidity.Source.Expr.var "to",
                                     SolidCore.Solidity.Source.Expr.var "value"],
                                  SolidCore.Solidity.Source.Stmt.returnValues [SolidCore.Solidity.Source.Expr.word 1]]],
                    dispatchId? := none },
                  { name := "approve",
                    selector? := some 157198259,
                    payable := false,
                    params := [{ name := "spender", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "value", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.bool, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "value")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "value")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.assign
                                    (SolidCore.Solidity.Source.LValue.index
                                      (SolidCore.Solidity.Source.LValue.storageIndex
                                        "allowances"
                                        (SolidCore.Solidity.Source.Expr.caller))
                                      (SolidCore.Solidity.Source.Expr.var "spender"))
                                    (SolidCore.Solidity.Source.Expr.castOp
                                      (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                      256
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Approval"
                                    [SolidCore.Solidity.Source.Expr.caller,
                                     SolidCore.Solidity.Source.Expr.var "spender",
                                     SolidCore.Solidity.Source.Expr.var "value"],
                                  SolidCore.Solidity.Source.Stmt.returnValues [SolidCore.Solidity.Source.Expr.word 1]]],
                    dispatchId? := none },
                  { name := "transferFrom",
                    selector? := some 599290589,
                    payable := false,
                    params := [{ name := "from", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "to", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "value", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.bool, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "value")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "value")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.varDecl
                                    (SolidCore.Solidity.Source.Ty.uint256)
                                    "a"
                                    (some (SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.index
                                         (SolidCore.Solidity.Source.Expr.storageRead
                                           (SolidCore.Solidity.Source.StorageReadMode.element)
                                           "allowances"
                                           [SolidCore.Solidity.Source.Expr.var "from"])
                                         (SolidCore.Solidity.Source.Expr.caller)))),
                                  SolidCore.Solidity.Source.Stmt.ifElse
                                    (SolidCore.Solidity.Source.Expr.binary
                                      (SolidCore.Solidity.Source.BinaryOp.lt)
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.var "a"))
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.var "value")))
                                    (SolidCore.Solidity.Source.Stmt.block
                                      [SolidCore.Solidity.Source.Stmt.revertError (some "allowance")])
                                    (SolidCore.Solidity.Source.Stmt.ifElse
                                      (SolidCore.Solidity.Source.Expr.binary
                                        (SolidCore.Solidity.Source.BinaryOp.ne)
                                        (SolidCore.Solidity.Source.Expr.castOp
                                          (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                          256
                                          (SolidCore.Solidity.Source.Expr.var "a"))
                                        (SolidCore.Solidity.Source.Expr.castOp
                                          (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                          256
                                          (SolidCore.Solidity.Source.Expr.word
                                            115792089237316195423570985008687907853269984665640564039457584007913129639935)))
                                      (SolidCore.Solidity.Source.Stmt.block
                                        [SolidCore.Solidity.Source.Stmt.assign
                                           (SolidCore.Solidity.Source.LValue.index
                                             (SolidCore.Solidity.Source.LValue.storageIndex
                                               "allowances"
                                               (SolidCore.Solidity.Source.Expr.var "from"))
                                             (SolidCore.Solidity.Source.Expr.caller))
                                           (SolidCore.Solidity.Source.Expr.castOp
                                             (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                             256
                                             (SolidCore.Solidity.Source.Expr.castOp
                                               (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                               256
                                               (SolidCore.Solidity.Source.Expr.binary
                                                 (SolidCore.Solidity.Source.BinaryOp.sub)
                                                 (SolidCore.Solidity.Source.Expr.castOp
                                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                   256
                                                   (SolidCore.Solidity.Source.Expr.var "a"))
                                                 (SolidCore.Solidity.Source.Expr.castOp
                                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                   256
                                                   (SolidCore.Solidity.Source.Expr.var "value")))))])
                                      (SolidCore.Solidity.Source.Stmt.skip)),
                                  SolidCore.Solidity.Source.Stmt.requireStmt
                                    (SolidCore.Solidity.Source.Expr.binary
                                      (SolidCore.Solidity.Source.BinaryOp.ge)
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.storageRead
                                          (SolidCore.Solidity.Source.StorageReadMode.element)
                                          "balances"
                                          [SolidCore.Solidity.Source.Expr.var "from"]))
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.var "value")))
                                    none,
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.sub))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "balances"
                                        [SolidCore.Solidity.Source.Expr.var "from"])
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "balances"
                                        [SolidCore.Solidity.Source.Expr.var "to"])
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Transfer"
                                    [SolidCore.Solidity.Source.Expr.var "from",
                                     SolidCore.Solidity.Source.Expr.var "to",
                                     SolidCore.Solidity.Source.Expr.var "value"],
                                  SolidCore.Solidity.Source.Stmt.returnValues [SolidCore.Solidity.Source.Expr.word 1]]],
                    dispatchId? := none },
                  { name := "__internal_balanceOf(address)#[SolidCore.Solidity.Ty.address false]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "who", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.element)
                                         "balances"
                                         [SolidCore.Solidity.Source.Expr.var "who"])]]],
                    dispatchId? := none },
                  { name := "__internal_allowance(address,address)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.address false]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "holder", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "spender", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.index
                                         (SolidCore.Solidity.Source.Expr.storageRead
                                           (SolidCore.Solidity.Source.StorageReadMode.element)
                                           "allowances"
                                           [SolidCore.Solidity.Source.Expr.var "holder"])
                                         (SolidCore.Solidity.Source.Expr.var "spender"))]]],
                    dispatchId? := none },
                  { name := "__internal_getOwner()#[]",
                    selector? := none,
                    payable := false,
                    params := [],
                    paramAbiCleanups := [],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.storageRead
                                       (SolidCore.Solidity.Source.StorageReadMode.ref)
                                       "owner"
                                       []]]],
                    dispatchId? := none },
                  { name := "__internal_isFrozen(address)#[SolidCore.Solidity.Ty.address false]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "who", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.bool, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.storageRead
                                       (SolidCore.Solidity.Source.StorageReadMode.element)
                                       "frozen"
                                       [SolidCore.Solidity.Source.Expr.var "who"]]]],
                    dispatchId? := none },
                  { name := "__internal_freeze(address)#[SolidCore.Solidity.Ty.address false]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "who", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.requireStmt
                                    (SolidCore.Solidity.Source.Expr.binary
                                      (SolidCore.Solidity.Source.BinaryOp.eq)
                                      (SolidCore.Solidity.Source.Expr.caller)
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.ref)
                                        "owner"
                                        []))
                                    none,
                                  SolidCore.Solidity.Source.Stmt.assign
                                    (SolidCore.Solidity.Source.LValue.storageIndex
                                      "frozen"
                                      (SolidCore.Solidity.Source.Expr.var "who"))
                                    (SolidCore.Solidity.Source.Expr.word 1)]],
                    dispatchId? := none },
                  { name := "__internal_transfer(address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "to", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "value", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.bool, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "value")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "value")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.requireStmt
                                    (SolidCore.Solidity.Source.Expr.unary
                                      (SolidCore.Solidity.Source.UnaryOp.logicalNot)
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "frozen"
                                        [SolidCore.Solidity.Source.Expr.caller]))
                                    none,
                                  SolidCore.Solidity.Source.Stmt.requireStmt
                                    (SolidCore.Solidity.Source.Expr.binary
                                      (SolidCore.Solidity.Source.BinaryOp.ge)
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.storageRead
                                          (SolidCore.Solidity.Source.StorageReadMode.element)
                                          "balances"
                                          [SolidCore.Solidity.Source.Expr.caller]))
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.var "value")))
                                    (some "balance"),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.sub))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "balances"
                                        [SolidCore.Solidity.Source.Expr.caller])
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "balances"
                                        [SolidCore.Solidity.Source.Expr.var "to"])
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Transfer"
                                    [SolidCore.Solidity.Source.Expr.caller,
                                     SolidCore.Solidity.Source.Expr.var "to",
                                     SolidCore.Solidity.Source.Expr.var "value"],
                                  SolidCore.Solidity.Source.Stmt.returnValues [SolidCore.Solidity.Source.Expr.word 1]]],
                    dispatchId? := none },
                  { name := "__internal_approve(address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "spender", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "value", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.bool, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "value")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "value")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.assign
                                    (SolidCore.Solidity.Source.LValue.index
                                      (SolidCore.Solidity.Source.LValue.storageIndex
                                        "allowances"
                                        (SolidCore.Solidity.Source.Expr.caller))
                                      (SolidCore.Solidity.Source.Expr.var "spender"))
                                    (SolidCore.Solidity.Source.Expr.castOp
                                      (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                      256
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Approval"
                                    [SolidCore.Solidity.Source.Expr.caller,
                                     SolidCore.Solidity.Source.Expr.var "spender",
                                     SolidCore.Solidity.Source.Expr.var "value"],
                                  SolidCore.Solidity.Source.Stmt.returnValues [SolidCore.Solidity.Source.Expr.word 1]]],
                    dispatchId? := none },
                  { name := "__internal_transferFrom(address,address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "from", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "to", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "value", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.bool, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "value")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "value")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.varDecl
                                    (SolidCore.Solidity.Source.Ty.uint256)
                                    "a"
                                    (some (SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.index
                                         (SolidCore.Solidity.Source.Expr.storageRead
                                           (SolidCore.Solidity.Source.StorageReadMode.element)
                                           "allowances"
                                           [SolidCore.Solidity.Source.Expr.var "from"])
                                         (SolidCore.Solidity.Source.Expr.caller)))),
                                  SolidCore.Solidity.Source.Stmt.ifElse
                                    (SolidCore.Solidity.Source.Expr.binary
                                      (SolidCore.Solidity.Source.BinaryOp.lt)
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.var "a"))
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.var "value")))
                                    (SolidCore.Solidity.Source.Stmt.block
                                      [SolidCore.Solidity.Source.Stmt.revertError (some "allowance")])
                                    (SolidCore.Solidity.Source.Stmt.ifElse
                                      (SolidCore.Solidity.Source.Expr.binary
                                        (SolidCore.Solidity.Source.BinaryOp.ne)
                                        (SolidCore.Solidity.Source.Expr.castOp
                                          (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                          256
                                          (SolidCore.Solidity.Source.Expr.var "a"))
                                        (SolidCore.Solidity.Source.Expr.castOp
                                          (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                          256
                                          (SolidCore.Solidity.Source.Expr.word
                                            115792089237316195423570985008687907853269984665640564039457584007913129639935)))
                                      (SolidCore.Solidity.Source.Stmt.block
                                        [SolidCore.Solidity.Source.Stmt.assign
                                           (SolidCore.Solidity.Source.LValue.index
                                             (SolidCore.Solidity.Source.LValue.storageIndex
                                               "allowances"
                                               (SolidCore.Solidity.Source.Expr.var "from"))
                                             (SolidCore.Solidity.Source.Expr.caller))
                                           (SolidCore.Solidity.Source.Expr.castOp
                                             (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                             256
                                             (SolidCore.Solidity.Source.Expr.castOp
                                               (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                               256
                                               (SolidCore.Solidity.Source.Expr.binary
                                                 (SolidCore.Solidity.Source.BinaryOp.sub)
                                                 (SolidCore.Solidity.Source.Expr.castOp
                                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                   256
                                                   (SolidCore.Solidity.Source.Expr.var "a"))
                                                 (SolidCore.Solidity.Source.Expr.castOp
                                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                   256
                                                   (SolidCore.Solidity.Source.Expr.var "value")))))])
                                      (SolidCore.Solidity.Source.Stmt.skip)),
                                  SolidCore.Solidity.Source.Stmt.requireStmt
                                    (SolidCore.Solidity.Source.Expr.binary
                                      (SolidCore.Solidity.Source.BinaryOp.ge)
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.storageRead
                                          (SolidCore.Solidity.Source.StorageReadMode.element)
                                          "balances"
                                          [SolidCore.Solidity.Source.Expr.var "from"]))
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.var "value")))
                                    none,
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.sub))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "balances"
                                        [SolidCore.Solidity.Source.Expr.var "from"])
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "balances"
                                        [SolidCore.Solidity.Source.Expr.var "to"])
                                      (SolidCore.Solidity.Source.Expr.var "value")),
                                  SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Transfer"
                                    [SolidCore.Solidity.Source.Expr.var "from",
                                     SolidCore.Solidity.Source.Expr.var "to",
                                     SolidCore.Solidity.Source.Expr.var "value"],
                                  SolidCore.Solidity.Source.Stmt.returnValues [SolidCore.Solidity.Source.Expr.word 1]]],
                    dispatchId? := none }] }

/-! ## The selectors and the events' signature topics

The type checker computes each external function's selector and each event's topic by
Keccak-256, which costs the kernel about 400 MB a hash: each is checked once, alone, and the
check of the shape below runs on copies that read them from tables. -/

/-- The selector of `balanceOf(address)`, by Keccak-256 of its signature. -/
def selBalanceOf : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "balanceOf(address)"

kernel_rfl selBalanceOf_eq selBalanceOf balanceOfSel

/-- The selector of `allowance(address,address)`, by Keccak-256 of its signature. -/
def selAllowance : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "allowance(address,address)"

kernel_rfl selAllowance_eq selAllowance allowanceSel

/-- The selector of `getOwner()`, by Keccak-256 of its signature. -/
def selGetOwner : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "getOwner()"

kernel_rfl selGetOwner_eq selGetOwner getOwnerSel

/-- The selector of `isFrozen(address)`, by Keccak-256 of its signature. -/
def selIsFrozen : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "isFrozen(address)"

kernel_rfl selIsFrozen_eq selIsFrozen isFrozenSel

/-- The selector of `freeze(address)`, by Keccak-256 of its signature. -/
def selFreeze : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "freeze(address)"

kernel_rfl selFreeze_eq selFreeze freezeSel

/-- The selector of `transfer(address,uint256)`, by Keccak-256 of its signature. -/
def selTransfer : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "transfer(address,uint256)"

kernel_rfl selTransfer_eq selTransfer transferSel

/-- The selector of `approve(address,uint256)`, by Keccak-256 of its signature. -/
def selApprove : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "approve(address,uint256)"

kernel_rfl selApprove_eq selApprove approveSel

/-- The selector of `transferFrom(address,address,uint256)`, by Keccak-256 of its signature. -/
def selTransferFrom : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "transferFrom(address,address,uint256)"

kernel_rfl selTransferFrom_eq selTransferFrom transferFromSel

/-- The topic of `Transfer(address,address,uint256)`, by Keccak-256 of its signature. -/
def topicTransfer : Nat := SolidCore.Solidity.Source.Keccak.digestWord "Transfer(address,address,uint256)"

kernel_rfl topicTransfer_eq topicTransfer 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef

/-- The topic of `Approval(address,address,uint256)`, by Keccak-256 of its signature. -/
def topicApproval : Nat := SolidCore.Solidity.Source.Keccak.digestWord "Approval(address,address,uint256)"

kernel_rfl topicApproval_eq topicApproval 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925

/-- `ABI.selectorFromSignature`, with `Token`'s signatures by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "balanceOf(address)" then balanceOfSel
  else if s = "allowance(address,address)" then allowanceSel
  else if s = "getOwner()" then getOwnerSel
  else if s = "isFrozen(address)" then isFrozenSel
  else if s = "freeze(address)" then freezeSel
  else if s = "transfer(address,uint256)" then transferSel
  else if s = "approve(address,uint256)" then approveSel
  else if s = "transferFrom(address,address,uint256)" then transferFromSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split
  · next h => subst h; exact selBalanceOf_eq
  · split
    · next h => subst h; exact selAllowance_eq
    · split
      · next h => subst h; exact selGetOwner_eq
      · split
        · next h => subst h; exact selIsFrozen_eq
        · split
          · next h => subst h; exact selFreeze_eq
          · split
            · next h => subst h; exact selTransfer_eq
            · split
              · next h => subst h; exact selApprove_eq
              · split
                · next h => subst h; exact selTransferFrom_eq
                · rfl

/-- `Keccak.digestWord`, with the events' signatures by table. -/
def digestTable (s : String) : Nat :=
  if s = "Transfer(address,address,uint256)" then 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
  else if s = "Approval(address,address,uint256)" then 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925
  else SolidCore.Solidity.Source.Keccak.digestWord s

theorem digest_eq : SolidCore.Solidity.Source.Keccak.digestWord = digestTable := by
  funext s
  unfold digestTable
  split
  · next h => subst h; exact topicTransfer_eq
  · split
    · next h => subst h; exact topicApproval_eq
    · rfl

/-- SolidCore's checked core of `Token`, and whether its constructor leaves no storage and no
logs, when `Token` type checks. -/
def shape? : Option (Contract × Bool) :=
  match contract? with
  | .ok c => some (c.core, Wide.deployedAt fuel c [])
  | .error _ => none

-- `shape_eq : shape? = some (coreLit, true)`: `Token` type checks, its core is `coreLit` and its
-- constructor leaves no storage, by the kernel's conversion check on the copy of `shape?` that
-- reads the selectors and the topics from their tables.
kernel_rfl shape_eq shape? (some (coreLit, true)) using selector_eq digest_eq

/-! ## The check on solar's module -/

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `balanceOf`. -/
theorem check_balanceOf :
    Generic.check fuel mirFuel coreLit stage0 [fnBalanceOf] .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `allowance`. -/
theorem check_allowance :
    Generic.check fuel mirFuel coreLit stage0 [fnAllowance] .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `getOwner`. -/
theorem check_getOwner :
    Generic.check fuel mirFuel coreLit stage0 [fnGetOwner] .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `isFrozen`. -/
theorem check_isFrozen :
    Generic.check fuel mirFuel coreLit stage0 [fnIsFrozen] .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `freeze`. -/
theorem check_freeze :
    Generic.check fuel mirFuel coreLit stage0 [fnFreeze] .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `transfer`. -/
theorem check_transfer :
    Generic.check fuel mirFuel coreLit stage0 [fnTransfer] .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `approve`. -/
theorem check_approve :
    Generic.check fuel mirFuel coreLit stage0 [fnApprove] .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `transferFrom`. -/
theorem check_transferFrom :
    Generic.check fuel mirFuel coreLit stage0 [fnTransferFrom] .all = true := by
  decide +kernel

/-- The generic check accepts stage0 for every external function. -/
theorem check_stage0 :
    Generic.check fuel mirFuel coreLit stage0 fns .all = true := by
  have h0 := check_balanceOf
  have h1 := check_allowance
  have h2 := check_getOwner
  have h3 := check_isFrozen
  have h4 := check_freeze
  have h5 := check_transfer
  have h6 := check_approve
  have h7 := check_transferFrom
  simp only [Generic.check, List.all_cons, List.all_nil, Bool.and_true] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [Generic.check, fns, List.all_cons, List.all_nil, Bool.and_true, h0, h1, h2, h3, h4, h5, h6, h7]

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: no function is payable, and stage0 reverts with empty output on a
call of each with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue mirFuel coreLit stage0 fns .all = true := by
  decide +kernel

/-! ## Mutants the check rejects -/

/-- stage0 with each instruction of function `i` changed by `f`. -/
def mapFn (i : Nat) (f : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst) :
    SolarTV.MIR.Lowered.Module :=
  { stage0 with
    functions := stage0.functions.mapIdx fun j fn =>
      if j = i then { fn with blocks := fn.blocks.map fun b => { b with insts := b.insts.map f } }
      else fn }

/-- `allowance` hashing its two keys in the other order: the entry at
`keccak256(holder, keccak256(spender, 1))`, not `keccak256(spender, keccak256(holder, 1))`. -/
def swapKeys : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none .mstore [.const 0, .value 14] => .effect none .mstore [.const 0, .value 18]
  | .effect none .mstore [.const 0, .value 18] => .effect none .mstore [.const 0, .value 14]
  | i => i

/-- `transfer` without its `require(!frozen[msg.sender])`: the frozen flag read as zero. -/
def noFrozen : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .ne d (.value 90) b => .ne d (.const 0) b
  | i => i

/-- `approve`'s log with another first topic. -/
def wrongApproval : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none (.log 3) [a, b, .const t, c, d] => .effect none (.log 3) [a, b, .const (t + 1), c, d]
  | i => i

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `allowance` with its keys hashed in the other
order. -/
theorem check_rejects_map2 :
    Generic.check fuel mirFuel coreLit (mapFn 1 swapKeys) [fnAllowance] .all = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `transfer` without its `frozen` check. -/
theorem check_rejects_frozen :
    Generic.check fuel mirFuel coreLit (mapFn 5 noFrozen) [fnTransfer] .all = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `approve` with the wrong `Approval` topic. -/
theorem check_rejects_approval :
    Generic.check fuel mirFuel coreLit (mapFn 6 wrongApproval) [fnApprove] .all = false := by
  decide +kernel

/-! ## The stage -/

/-- The checked contract has the core `coreLit`, and its constructor leaves no storage. -/
theorem deployed_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core = coreLit ∧ ∃ d, Wide.DeployedAt fuel c d [] := by
  have h := shape_eq
  unfold shape? at h
  rw [hc] at h
  obtain ⟨hk, hd⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hk, Wide.deployedAt_of hd⟩

/-- **The source stage of `Token`**: every call of its eight external functions on any argument
words, no value, from any storage, under every oracle whose caller is SolidCore's and whose
Keccak-256 of two words is SolidCore's (`Generic.SourceEnvOk`). -/
theorem lowering (o : SolarTV.Machine.Oracle) (henv : Generic.SourceEnvOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c stage0
      (fun call => ∃ σ, fullScope fns σ call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageEnv o henv hd (by rw [hk]; exact check_stage0)

/-- **The source stage of `Token` at every value**: the same calls with any value below `2 ^ 256`:
no function is payable, and both sides revert with empty data. -/
theorem loweringValue (o : SolarTV.Machine.Oracle) (henv : Generic.SourceEnvOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c stage0
      (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageValueEnv o henv hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

#print axioms selector_eq

#print axioms digest_eq

#print axioms shape_eq

#print axioms check_stage0

#print axioms checkValue_stage0

#print axioms check_rejects_map2

#print axioms check_rejects_frozen

#print axioms check_rejects_approval

#print axioms lowering

#print axioms loweringValue

end SolidCore.Refinement.Solar.Token
