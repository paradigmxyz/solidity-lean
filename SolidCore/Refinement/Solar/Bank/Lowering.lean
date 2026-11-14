import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.KernelCopies
import SolidCore.Refinement.KernelRfl
import SolidCore.Refinement.Source.Bank
import bank.gen.Bank.Stage0

/-!
# bank: the generic source stage on solar's own module

solar-tv/milestone/bank/bank.sol (sha256
2a29919999674ac221097e3f50ed43bcddf094d19a08da5f5c9704a0dd099d03, copied to
scripts/refinement/bank/bank.sol),

    contract Bank { mapping(address => uint256) balances; uint256 total;
      event Deposit(address indexed who, uint256 amount);
      function credit(address who, uint256 amount) internal returns (uint256) {
        balances[who] += amount; total += amount; return balances[who]; }
      function deposit(uint256 amount) external returns (uint256) {
        uint256 b = credit(msg.sender, amount); emit Deposit(msg.sender, amount); return b; }
      function depositFor(address who, uint256 amount) external returns (uint256) {
        return credit(who, amount); }
      function balanceOf(address who) external view returns (uint256) { return balances[who]; } }

has a mapping from addresses, whose entries live at `keccak256(abi.encode(key, 0))`, an
internal function that both `deposit` (for `msg.sender`) and `depositFor` call, checked
additions into the entry and into `total`, and an event with an indexed address.
`SolarTV.Export.Bank.stage0` is solar's first lowered MIR module for it (solar 0a455fda,
-Ogas, osaka), from solar's solar-tv/milestone/bank, the module whose backend stages solar's
milestone proves (`SolarTV.Milestone.Bank.bank_mir_to_evmir`). Its `credit` is an internal
function of the module, called with `call` and left with `leave`; it hashes memory words 0
and 1 for the entry's slot; `deposit` reads `caller` and logs with `log 2`; the facts it
relies on (`assume`: the address words fit in 160 bits) follow from the path's checks.

SolidCore's core (`coreLit`, solc 0.8.35's AST through scripts/solc_ast_to_lean_source.py into
Source/Bank.lean and `TypeCheck.CheckedInput.contract`, printed and copied) inlines no call:
its `internalCall` runs `credit`'s body in a frame of its own. The generic check erases it
by inlining (`Generic.eraseStmt`) and runs the module symbolically with the environment flag
(`Generic.symTree … .all`): the caller is `callerWord`, a mapping slot the word
`hash key slot`, storage at a computed slot a select on the slot words. Both trees agree in
canonical form for every function.

* `shape_eq`: `Bank` type checks, its core is `coreLit`, its constructor leaves no storage;
* `check_stage0`, `checkValue_stage0`: the generic check accepts stage0 for the three
  external functions, at no value and at any value (`decide +kernel`);
* `check_rejects_slot`, `check_rejects_caller`, `check_rejects_topic`: it rejects stage0
  with `credit`'s mapping slot 1 for 0, with `deposit`'s caller replaced by its argument, and
  with the `Deposit` topic changed;
* `lowering`, `loweringValue`: the stage from SolidCore to stage0 on every call of the three
  functions, from any storage, under every oracle with SolidCore's caller and hash of two words
  (`Generic.SourceEnvOk`).

No sorry, native_decide or bv_decide.
-/

namespace SolidCore.Refinement.Solar.Bank

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- The interpreter fuel of the symbolic run of the module: steps along each path. -/
def mirFuel : Nat := 40

/-- SolidCore's checked `Bank`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.Bank.importedSourceUnit "Bank"

/-- The selector of `deposit(uint256)`. -/
abbrev depositSel : Nat := 0xb6b55f25

/-- The selector of `depositFor(address,uint256)`. -/
abbrev depositForSel : Nat := 0x2f4f21e2

/-- The selector of `balanceOf(address)`. -/
abbrev balanceOfSel : Nat := 0x70a08231

/-- `deposit` and its parameter. -/
def fnDeposit : Fn := ⟨depositSel, [.uint 256]⟩

/-- `depositFor` and its parameters (an address is a word of 160 bits). -/
def fnDepositFor : Fn := ⟨depositForSel, [.uint 160, .uint 256]⟩

/-- `balanceOf` and its parameter. -/
def fnBalanceOf : Fn := ⟨balanceOfSel, [.uint 160]⟩

/-- The external functions of `Bank`. -/
def fns : List Fn := [fnDeposit, fnDepositFor, fnBalanceOf]

/-- SolidCore's core contract of `Bank`, as the type checker leaves it. -/
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
                      { name := "total",
                        slot := 1,
                        ty? := some (SolidCore.Solidity.Source.Ty.uint256),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.uint256)),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 32,
                        packedSigned := false }],
    immutableFields := [],
    eventDecls := [{ name := "Deposit",
                     indexedCount := 1,
                     topic? := some 102222681472383059465863322013072701928378550215632170212813623808969952268444,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false }] },
                   { name := "Bank.Deposit",
                     indexedCount := 1,
                     topic? := some 102222681472383059465863322013072701928378550215632170212813623808969952268444,
                     fields := [{ ty := SolidCore.Solidity.Source.Ty.address, indexed := true },
                                { ty := SolidCore.Solidity.Source.Ty.uint256, indexed := false }] }],
    errorDecls := [],
    functions := [{ name := "deposit",
                    selector? := some 3065339685,
                    payable := false,
                    params := [{ name := "amount", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "amount")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "amount")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.varDecl
                                    (SolidCore.Solidity.Source.Ty.uint256)
                                    "_sol_hoist_0"
                                    none,
                                  SolidCore.Solidity.Source.Stmt.block
                                    [SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.address)
                                       "_ic_arg_0"
                                       (some (SolidCore.Solidity.Source.Expr.caller)),
                                     SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.uint256)
                                       "_ic_arg_1"
                                       (some (SolidCore.Solidity.Source.Expr.castOp
                                          (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                          256
                                          (SolidCore.Solidity.Source.Expr.var "amount"))),
                                     SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.uint256)
                                       "_ret_credit_0"
                                       none,
                                     SolidCore.Solidity.Source.Stmt.captureReturn
                                       ["_ret_credit_0"]
                                       (SolidCore.Solidity.Source.Stmt.internalCall
                                         ["_ret_credit_0"]
                                         "__internal_credit(address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]"
                                         [SolidCore.Solidity.Source.Expr.var "_ic_arg_0",
                                          SolidCore.Solidity.Source.Expr.var "_ic_arg_1"]),
                                     SolidCore.Solidity.Source.Stmt.assign
                                       (SolidCore.Solidity.Source.LValue.var "_sol_hoist_0")
                                       (SolidCore.Solidity.Source.Expr.var "_ret_credit_0")],
                                  SolidCore.Solidity.Source.Stmt.varDecl
                                    (SolidCore.Solidity.Source.Ty.uint256)
                                    "b"
                                    (some (SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.var "_sol_hoist_0"))),
                                  SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Deposit"
                                    [SolidCore.Solidity.Source.Expr.caller, SolidCore.Solidity.Source.Expr.var "amount"],
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.var "b")]]],
                    dispatchId? := none },
                  { name := "depositFor",
                    selector? := some 793715170,
                    payable := false,
                    params := [{ name := "who", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "amount", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "amount")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "amount")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.varDecl
                                    (SolidCore.Solidity.Source.Ty.uint256)
                                    "_sol_hoist_0"
                                    none,
                                  SolidCore.Solidity.Source.Stmt.block
                                    [SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.address)
                                       "_ic_arg_0"
                                       (some (SolidCore.Solidity.Source.Expr.var "who")),
                                     SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.uint256)
                                       "_ic_arg_1"
                                       (some (SolidCore.Solidity.Source.Expr.castOp
                                          (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                          256
                                          (SolidCore.Solidity.Source.Expr.var "amount"))),
                                     SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.uint256)
                                       "_ret_credit_0"
                                       none,
                                     SolidCore.Solidity.Source.Stmt.captureReturn
                                       ["_ret_credit_0"]
                                       (SolidCore.Solidity.Source.Stmt.internalCall
                                         ["_ret_credit_0"]
                                         "__internal_credit(address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]"
                                         [SolidCore.Solidity.Source.Expr.var "_ic_arg_0",
                                          SolidCore.Solidity.Source.Expr.var "_ic_arg_1"]),
                                     SolidCore.Solidity.Source.Stmt.assign
                                       (SolidCore.Solidity.Source.LValue.var "_sol_hoist_0")
                                       (SolidCore.Solidity.Source.Expr.var "_ret_credit_0")],
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.var "_sol_hoist_0")]]],
                    dispatchId? := none },
                  { name := "balanceOf",
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
                  { name := "__internal_credit(address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "who", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "amount", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "amount")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "amount")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.element)
                                        "balances"
                                        [SolidCore.Solidity.Source.Expr.var "who"])
                                      (SolidCore.Solidity.Source.Expr.var "amount")),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "total"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "amount")),
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.element)
                                         "balances"
                                         [SolidCore.Solidity.Source.Expr.var "who"])]]],
                    dispatchId? := none },
                  { name := "__internal_deposit(uint256)#[SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "amount", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "amount")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "amount")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.varDecl
                                    (SolidCore.Solidity.Source.Ty.uint256)
                                    "_sol_hoist_0"
                                    none,
                                  SolidCore.Solidity.Source.Stmt.block
                                    [SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.address)
                                       "_ic_arg_0"
                                       (some (SolidCore.Solidity.Source.Expr.caller)),
                                     SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.uint256)
                                       "_ic_arg_1"
                                       (some (SolidCore.Solidity.Source.Expr.castOp
                                          (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                          256
                                          (SolidCore.Solidity.Source.Expr.var "amount"))),
                                     SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.uint256)
                                       "_ret_credit_0"
                                       none,
                                     SolidCore.Solidity.Source.Stmt.captureReturn
                                       ["_ret_credit_0"]
                                       (SolidCore.Solidity.Source.Stmt.internalCall
                                         ["_ret_credit_0"]
                                         "__internal_credit(address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]"
                                         [SolidCore.Solidity.Source.Expr.var "_ic_arg_0",
                                          SolidCore.Solidity.Source.Expr.var "_ic_arg_1"]),
                                     SolidCore.Solidity.Source.Stmt.assign
                                       (SolidCore.Solidity.Source.LValue.var "_sol_hoist_0")
                                       (SolidCore.Solidity.Source.Expr.var "_ret_credit_0")],
                                  SolidCore.Solidity.Source.Stmt.varDecl
                                    (SolidCore.Solidity.Source.Ty.uint256)
                                    "b"
                                    (some (SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.var "_sol_hoist_0"))),
                                  SolidCore.Solidity.Source.Stmt.emitEvent
                                    "Deposit"
                                    [SolidCore.Solidity.Source.Expr.caller, SolidCore.Solidity.Source.Expr.var "amount"],
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.var "b")]]],
                    dispatchId? := none },
                  { name := "__internal_depositFor(address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "who", ty := SolidCore.Solidity.Source.Ty.address, isStorageRef := false },
                               { name := "amount", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.none,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "amount")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "amount")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.varDecl
                                    (SolidCore.Solidity.Source.Ty.uint256)
                                    "_sol_hoist_0"
                                    none,
                                  SolidCore.Solidity.Source.Stmt.block
                                    [SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.address)
                                       "_ic_arg_0"
                                       (some (SolidCore.Solidity.Source.Expr.var "who")),
                                     SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.uint256)
                                       "_ic_arg_1"
                                       (some (SolidCore.Solidity.Source.Expr.castOp
                                          (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                          256
                                          (SolidCore.Solidity.Source.Expr.var "amount"))),
                                     SolidCore.Solidity.Source.Stmt.varDecl
                                       (SolidCore.Solidity.Source.Ty.uint256)
                                       "_ret_credit_0"
                                       none,
                                     SolidCore.Solidity.Source.Stmt.captureReturn
                                       ["_ret_credit_0"]
                                       (SolidCore.Solidity.Source.Stmt.internalCall
                                         ["_ret_credit_0"]
                                         "__internal_credit(address,uint256)#[SolidCore.Solidity.Ty.address false, SolidCore.Solidity.Ty.uint 256]"
                                         [SolidCore.Solidity.Source.Expr.var "_ic_arg_0",
                                          SolidCore.Solidity.Source.Expr.var "_ic_arg_1"]),
                                     SolidCore.Solidity.Source.Stmt.assign
                                       (SolidCore.Solidity.Source.LValue.var "_sol_hoist_0")
                                       (SolidCore.Solidity.Source.Expr.var "_ret_credit_0")],
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.var "_sol_hoist_0")]]],
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
                    dispatchId? := none }] }

/-! ## The selectors and the event's signature topic

The type checker computes each external function's selector and the event's topic by
Keccak-256, which costs the kernel about 400 MB a hash: each is checked once, alone, and the
check of the shape below runs on copies that read them from tables. -/
/-- The selector of `deposit(uint256)`, by Keccak-256 of its signature. -/
def selDeposit : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "deposit(uint256)"

kernel_rfl selDeposit_eq selDeposit depositSel
/-- The selector of `depositFor(address,uint256)`, by Keccak-256 of its signature. -/
def selDepositFor : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "depositFor(address,uint256)"

kernel_rfl selDepositFor_eq selDepositFor depositForSel
/-- The selector of `balanceOf(address)`, by Keccak-256 of its signature. -/
def selBalanceOf : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "balanceOf(address)"

kernel_rfl selBalanceOf_eq selBalanceOf balanceOfSel
/-- The topic of `Deposit(address,uint256)`, by Keccak-256 of its signature. -/
def topic : Nat := SolidCore.Solidity.Source.Keccak.digestWord "Deposit(address,uint256)"

kernel_rfl topic_eq topic 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c

/-- `ABI.selectorFromSignature`, with `Bank`'s signatures by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "deposit(uint256)" then depositSel
  else if s = "depositFor(address,uint256)" then depositForSel
  else if s = "balanceOf(address)" then balanceOfSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split
  · next h => subst h; exact selDeposit_eq
  · split
    · next h => subst h; exact selDepositFor_eq
    · split
      · next h => subst h; exact selBalanceOf_eq
      · rfl

/-- `Keccak.digestWord`, with the event's signature by table. -/
def digestTable (s : String) : Nat :=
  if s = "Deposit(address,uint256)" then 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c else SolidCore.Solidity.Source.Keccak.digestWord s

theorem digest_eq : SolidCore.Solidity.Source.Keccak.digestWord = digestTable := by
  funext s
  unfold digestTable
  split
  · next h => subst h; exact topic_eq
  · rfl

/-- SolidCore's checked core of `Bank`, and whether its constructor leaves no storage and no
logs, when `Bank` type checks. -/
def shape? : Option (Contract × Bool) :=
  match contract? with
  | .ok c => some (c.core, Wide.deployedAt fuel c [])
  | .error _ => none

-- `shape_eq : shape? = some (coreLit, true)`: `Bank` type checks, its core is `coreLit` and its
-- constructor leaves no storage, by the kernel's conversion check on the copy of `shape?` that
-- reads the selectors and the topic from their tables.
kernel_rfl shape_eq shape? (some (coreLit, true)) using selector_eq digest_eq

/-! ## The check on solar's module -/
set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `deposit`. -/
theorem check_deposit :
    Generic.check fuel mirFuel coreLit SolarTV.Export.Bank.stage0 [fnDeposit] .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `depositFor`. -/
theorem check_depositFor :
    Generic.check fuel mirFuel coreLit SolarTV.Export.Bank.stage0 [fnDepositFor] .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `balanceOf`. -/
theorem check_balanceOf :
    Generic.check fuel mirFuel coreLit SolarTV.Export.Bank.stage0 [fnBalanceOf] .all = true := by
  decide +kernel

/-- The generic check accepts stage0 for every external function. -/
theorem check_stage0 :
    Generic.check fuel mirFuel coreLit SolarTV.Export.Bank.stage0 fns .all = true := by
  have h0 := check_deposit
  have h1 := check_depositFor
  have h2 := check_balanceOf
  simp only [Generic.check, List.all_cons, List.all_nil, Bool.and_true] at h0 h1 h2
  simp only [Generic.check, fns, List.all_cons, List.all_nil, Bool.and_true, h0, h1, h2]

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: no function is payable, and stage0 reverts with empty output on a
call of each with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue mirFuel coreLit SolarTV.Export.Bank.stage0 fns .all = true := by
  decide +kernel

/-! ## Mutants the check rejects -/

/-- stage0 with each instruction of function `i` changed by `f`. -/
def mapFn (i : Nat) (f : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst) :
    SolarTV.MIR.Lowered.Module :=
  { SolarTV.Export.Bank.stage0 with
    functions := SolarTV.Export.Bank.stage0.functions.mapIdx fun j fn =>
      if j = i then { fn with blocks := fn.blocks.map fun b => { b with insts := b.insts.map f } }
      else fn }
/-- `credit`'s mapping slot: the hash of the key and the word 1, not 0. -/
def wrongSlot : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none .mstore [.const 32, .const 0] => .effect none .mstore [.const 32, .const 1]
  | i => i

/-- `deposit` crediting its argument word instead of `msg.sender`. -/
def noCaller : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect (some 1) .caller [] => .effect (some 1) .calldataload [.const 4]
  | i => i

/-- `deposit`'s log with another first topic. -/
def wrongTopic : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none (.log 2) [a, b, .const t, c] => .effect none (.log 2) [a, b, .const (t + 1), c]
  | i => i

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `depositFor` with `credit`'s slot changed. -/
theorem check_rejects_slot :
    Generic.check fuel mirFuel coreLit (mapFn 0 wrongSlot) [fnDepositFor] .all = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `deposit` crediting its argument word. -/
theorem check_rejects_caller :
    Generic.check fuel mirFuel coreLit (mapFn 1 noCaller) [fnDeposit] .all = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `deposit` with the wrong topic. -/
theorem check_rejects_topic :
    Generic.check fuel mirFuel coreLit (mapFn 1 wrongTopic) [fnDeposit] .all = false := by
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

/-- **The source stage of `Bank`**: every call of `deposit`, `depositFor` and `balanceOf` on any argument words, no value,
from any storage, under every oracle whose caller is SolidCore's and whose Keccak-256 of two words
is SolidCore's (`Generic.SourceEnvOk`). -/
theorem lowering (o : SolarTV.Machine.Oracle) (henv : Generic.SourceEnvOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Bank.stage0 (fun call => ∃ σ, fullScope fns σ call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageEnv o henv hd (by rw [hk]; exact check_stage0)

/-- **The source stage of `Bank` at every value**: the same calls with any value below `2 ^ 256`: no function is payable, and both sides revert with empty data. -/
theorem loweringValue (o : SolarTV.Machine.Oracle) (henv : Generic.SourceEnvOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Bank.stage0 (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageValueEnv o henv hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

#print axioms selector_eq

#print axioms digest_eq

#print axioms shape_eq

#print axioms check_stage0

#print axioms checkValue_stage0

#print axioms check_rejects_slot

#print axioms check_rejects_caller

#print axioms check_rejects_topic

#print axioms lowering

#print axioms loweringValue

end SolidCore.Refinement.Solar.Bank
