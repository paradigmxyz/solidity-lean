import SolidCore.Solidity.Interface.ContractMetadata

namespace SolidCore.Solidity.Executable

mutual

/-- R2: typed lowering of a binary op with the env threaded into BOTH operands
    through the FULL env-aware recursion (`Expr.toCoreAsWithEnvFuel?`), so a
    nested narrow cast / negation / ternary inside an operand keeps its
    operand-width checked cleanup. `&&`/`||` recurse on both operands at
    `Ty.bool` (previously they fell to the env-less `toCore?`, dropping the
    operand-width Panic 0x11 of a nested comparison operand, e.g.
    `(a + b) < n && k < 3` with `uint8 a,b`). `<<`/`>>` keep the existing
    Direct-path handling (fall through by returning `none`). -/
def Expr.binaryToCoreWithEnvTypedFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) (op : BinaryOp) (lhs rhs : Expr) :
    Option (Ty × CoreExpr) :=
  match fuel with
  | 0 => none
  | Nat.succ fuel =>
  -- R2 fix-forward (uniswap-v2 UQ112x112 regression): a LITERAL-ONLY binary
  -- (`2 ** 112`, `1 << 8`, `10 * 1e18`) is a compile-time rational constant in
  -- solc (`RationalNumberType`, Types.cpp) — evaluated with UNBOUNDED
  -- precision and only the FINAL value checked against the target type. It
  -- must never reach this runtime typed lowering: the `**` arm below types
  -- the base at its MOBILE type (`2` → `uint8`), so the caller's
  -- operand-width cleanup would spuriously Panic 0x11 on
  -- `uint224 z = 2 ** 112` (UQ112x112.Q112). Return `none` so every caller
  -- falls back to the env-less constant folding (`toCoreNumericLiteralAs?` /
  -- `Expr.toCore?`), which folds exactly like solc (and out-of-range
  -- constants keep failing closed there).
  if Expr.isRawNumberLiteralExpression lhs &&
      Expr.isRawNumberLiteralExpression rhs then
    none
  else
  match op with
  | BinaryOp.boolAnd
  | BinaryOp.boolOr => do
      let coreOp ← BinaryOp.toCore? op
      let lhsCore ← Expr.toCoreAsWithEnvFuel? fuel storageNames env Ty.bool lhs
      let rhsCore ← Expr.toCoreAsWithEnvFuel? fuel storageNames env Ty.bool rhs
      some
        (Ty.bool,
          SolidCore.Solidity.Source.Expr.binary coreOp lhsCore rhsCore)
  | BinaryOp.shl
  | BinaryOp.shr => none
  | BinaryOp.exp => do
      -- EXP-NARROW-BASE-WIDE-EXPONENT: `**` is NOT symmetric. Per solc
      -- (`IntegerType::binaryOperatorResult` / `Token::Exp`, `Types.cpp` ~728),
      -- the result type of `base ** e` is the BASE (left-operand) type ONLY —
      -- "ignoring the (larger) type of the second operand". The exponent keeps
      -- its OWN type and is NOT folded into a common-type computation. Lowering
      -- both operands + the result at the symmetric common type
      -- (`commonImplicit? uint8 uint16 = uint16`) would run the checked-exp /
      -- `implicitCleanupCore` at the wider width, where the uint8 overflow
      -- (`2 ** 8 = 256`) fits and its Panic 0x11 is silently lost. Instead
      -- lower the base at the base type (the returned `resultTy`, so the
      -- caller's operand-width `implicitCleanupCore` enforces the base bound)
      -- and the exponent at its own type (like solc's `cleanup_t_uintM` on the
      -- exponent — no coercion to the base type).
      let coreOp ← BinaryOp.toCore? op
      let baseTy0 ← Expr.abiTyWithEnv? env lhs
      let expTy0 ← Expr.abiTyWithEnv? env rhs
      let baseTy :=
        if Expr.isRawNumberLiteralExpression lhs then
          -- EXP-LITERAL-BASE-RUNTIME-EXPONENT (SOUNDNESS): a LITERAL base with
          -- a NON-literal exponent is typed by solc at the full 256-bit width —
          -- `RationalNumberType::binaryOperatorResult` (`Types.cpp`) resolves
          -- `<rational> ** <integer>` to `uint256` (`int256` for a negative
          -- literal base), NOT the literal's mobile type. Probe (solc 0.8.35):
          -- `uint8 e; uint8 r = 2**e;` → "Type uint256 is not implicitly
          -- convertible to uint8"; `int8 r = (-2)**e;` → int256 likewise. Using
          -- the mobile type (`2` → uint8) ran the checked exp at the NARROW
          -- width, spuriously Panicking 0x11 on `2**e` with `e = 8` (solc+EVM:
          -- 256) and `(-2)**e` with `e = 9` (solc+EVM: -512). NOTE the
          -- literal-base/literal-exponent case never reaches here — the
          -- raw-literal-only guard at the top of this function already returned
          -- `none`, so the compile-time constant fold (`2**255`, `2**112`)
          -- still handles it. A non-integer/out-of-range literal keeps
          -- `baseTy0` (mobile type `none`), preserving the existing
          -- fail-closed behavior.
          match Expr.untypedLiteralMobileTy? lhs with
          | some (Ty.int _) => Ty.int 256
          | some (Ty.uint _) => Ty.uint 256
          | _ => baseTy0
        else baseTy0
      let expTy :=
        if Expr.isRawNumberLiteralExpression rhs then
          (Expr.untypedLiteralMobileTy? rhs).getD expTy0
        else expTy0
      let baseCore ←
        Expr.toCoreAsWithEnvBitAwareFuel? fuel storageNames env baseTy lhs
      let expCore ←
        Expr.toCoreAsWithEnvBitAwareFuel? fuel storageNames env expTy rhs
      some
        (baseTy,
          SolidCore.Solidity.Source.Expr.binary coreOp baseCore expCore)
  | _ => do
      let coreOp ← BinaryOp.toCore? op
      let operandTy ← Expr.commonOperandTyWithEnv? env lhs rhs
      -- FB1: a `bytesN` operand that is itself a `<<`/`~` (e.g. `(b << 4) == …`,
      -- `(~b) == …`) must be lane-cleaned before the full-word comparison, or the
      -- bits `<<`/`~` pushed above the byte lane make the comparison diverge.
      let lhsCore ←
        Expr.toCoreAsWithEnvBitAwareFuel? fuel storageNames env operandTy lhs
      let rhsCore ←
        Expr.toCoreAsWithEnvBitAwareFuel? fuel storageNames env operandTy rhs
      let resultTy :=
        match op with
        | BinaryOp.lt | BinaryOp.gt | BinaryOp.le | BinaryOp.ge
        | BinaryOp.eq | BinaryOp.ne => Ty.bool
        | _ => operandTy
      some
        (resultTy,
          SolidCore.Solidity.Source.Expr.binary coreOp lhsCore rhsCore)

/-- Lower a `bytesN` shift/bitwise subtree while retaining env-aware evaluation
    of shift counts. The older non-recursive helper preserves bytes-lane
    cleanup but lowers shift counts through `toCore?`; consequently a count
    such as `uint8 a + b` runs at 256 bits and loses its checked overflow. -/
def Expr.toCoreFixedBytesBitOpWithEnvFuel? (fuel : Nat)
    (storageNames : List Name) (env : TypeEnv) (size : Nat) :
    Expr -> Option CoreExpr
  | expr =>
      match fuel with
      | 0 => Expr.toCoreFixedBytesBitOp? storageNames env size expr
      | Nat.succ fuel =>
          match expr with
          | Expr.binary BinaryOp.shl lhs rhs => do
              let lhsCore ←
                Expr.toCoreFixedBytesBitOpWithEnvFuel?
                  fuel storageNames env size lhs
              let rhsCore ←
                if Expr.abiArgNeedsEnvCleanup? rhs then do
                  let rhsTy ← Expr.abiTyWithEnv? env rhs
                  Expr.toCoreAsWithEnvFuel? fuel storageNames env rhsTy rhs
                else
                  Expr.toCore? storageNames rhs
              some
                (SolidCore.Solidity.Source.Expr.fixedBytesCast size size
                  (SolidCore.Solidity.Source.Expr.binary
                    SolidCore.Solidity.Source.BinaryOp.shl lhsCore rhsCore))
          | Expr.binary BinaryOp.shr lhs rhs => do
              let lhsCore ←
                Expr.toCoreFixedBytesBitOpWithEnvFuel?
                  fuel storageNames env size lhs
              let rhsCore ←
                if Expr.abiArgNeedsEnvCleanup? rhs then do
                  let rhsTy ← Expr.abiTyWithEnv? env rhs
                  Expr.toCoreAsWithEnvFuel? fuel storageNames env rhsTy rhs
                else
                  Expr.toCore? storageNames rhs
              some
                (SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.shr lhsCore rhsCore)
          | Expr.binary BinaryOp.bitAnd lhs rhs => do
              let lhsCore ←
                Expr.toCoreFixedBytesBitOpWithEnvFuel?
                  fuel storageNames env size lhs
              let rhsCore ←
                Expr.toCoreFixedBytesBitOpWithEnvFuel?
                  fuel storageNames env size rhs
              some
                (SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.bitAnd lhsCore rhsCore)
          | Expr.binary BinaryOp.bitOr lhs rhs => do
              let lhsCore ←
                Expr.toCoreFixedBytesBitOpWithEnvFuel?
                  fuel storageNames env size lhs
              let rhsCore ←
                Expr.toCoreFixedBytesBitOpWithEnvFuel?
                  fuel storageNames env size rhs
              some
                (SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.bitOr lhsCore rhsCore)
          | Expr.binary BinaryOp.bitXor lhs rhs => do
              let lhsCore ←
                Expr.toCoreFixedBytesBitOpWithEnvFuel?
                  fuel storageNames env size lhs
              let rhsCore ←
                Expr.toCoreFixedBytesBitOpWithEnvFuel?
                  fuel storageNames env size rhs
              some
                (SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.bitXor lhsCore rhsCore)
          | Expr.unary UnaryOp.bitNot inner => do
              let innerCore ←
                Expr.toCoreFixedBytesBitOpWithEnvFuel?
                  fuel storageNames env size inner
              some
                (SolidCore.Solidity.Source.Expr.fixedBytesCast size size
                  (SolidCore.Solidity.Source.Expr.unary
                    SolidCore.Solidity.Source.UnaryOp.bitNot innerCore))
          | expr =>
              Expr.toCoreAsWithEnvDirect?
                storageNames env (Ty.bytesN size) expr

/-- R2: fuel-carrying counterpart of `Expr.toCoreAsWithEnvBitAware?` that
    recurses into the FULL env-aware lowering for non-bit-op shapes (the
    non-fuel version stops at `Expr.toCoreAsWithEnvDirect?`, skipping the
    interceptor arms for children). -/
def Expr.toCoreAsWithEnvBitAwareFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) (targetTy : Ty) (expr : Expr) : Option CoreExpr :=
  match fuel with
  | 0 => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
  | Nat.succ fuel =>
  match Ty.fixedBytesSize? targetTy with
  | some size =>
      if Expr.isFixedBytesBitOpShape expr then
        Expr.toCoreFixedBytesBitOpWithEnvFuel?
          fuel storageNames env size expr
      else
        Expr.toCoreAsWithEnvFuel? fuel storageNames env targetTy expr
  | none => Expr.toCoreAsWithEnvFuel? fuel storageNames env targetTy expr

def Expr.toCoreAsWithEnvFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) (targetTy : Ty) (expr : Expr) : Option CoreExpr :=
  match fuel with
  | 0 => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
  | Nat.succ fuel =>
  -- FB1: a `bytesN`-targeted expression whose top node is a shift/bitwise op
  -- (e.g. `return (b << 4) >> 4;`, `bytes1 c = ~b;`) is lowered with per-op lane
  -- cleanup so bits pushed above the byte lane by `<<`/`~` are re-masked, exactly
  -- as solc's `cleanup_t_bytesN`. Non-`bytesN` targets and non-bit-op shapes fall
  -- through unchanged.
  match (match Ty.fixedBytesSize? targetTy with
    | some size =>
        if Expr.isFixedBytesBitOpShape expr then
          Expr.toCoreFixedBytesBitOpWithEnvFuel?
            fuel storageNames env size expr
        else
          none
    | none => none) with
  | some coreExpr => some coreExpr
  | none =>
  -- R2 fix-forward (uniswap-v2 UQ112x112 regression): a raw-literal CONSTANT
  -- expression (`2 ** 112`, `-(1e18)`, `~0`, and any literal-only arithmetic)
  -- is folded by solc at COMPILE TIME as an unbounded rational; only the
  -- final value is checked against the target type. Route it straight to
  -- `toCoreAsWithEnvDirect?` (whose `toCoreFixedBytesLiteralAs?` /
  -- `toCoreNumericLiteralAs?` chain folds it, and which keeps failing CLOSED
  -- for a non-fitting constant at an int/uint target) instead of the
  -- binary/unary runtime arms below, whose operand-width cleanup would
  -- spuriously Panic 0x11. EXCEPTION: an internal-function-typed target — a
  -- number literal there is a rewritten function-pointer dispatch ID
  -- (`rewriteInternalFnValueIdents`), which the dedicated literal arm below
  -- must keep handling.
  if Expr.isRawNumberLiteralExpression expr &&
      !(match targetTy with
        | Ty.functionWithLocations _ _ _ _ _ _ => true
        | _ => false) then
    Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
  else
  match Expr.toCoreIncDecWithEnv? env
      (Expr.toCoreLValue? storageNames) expr with
  | some coreExpr => some coreExpr
  | none =>
      match Expr.toCoreAssignOpWithEnv? storageNames env expr with
      | some coreExpr => some coreExpr
      | none =>
          match expr with
          | Expr.assign lhs AssignOp.assign rhs => do
              let lhsCore ← Expr.toCoreLValue? storageNames lhs
              let lhsTy ← Expr.abiTyWithEnv? env lhs
              let rhsCore ←
                Expr.toCoreAsWithEnvFuel? fuel storageNames env lhsTy rhs
              Expr.coreAsFromTy? targetTy lhsTy
                (SolidCore.Solidity.Source.Expr.assignExpr
                  lhsCore.toExpr rhsCore)
          | Expr.call (Expr.typeName (Ty.bytesN cbSize)) [Arg.positional argExpr]
          | Expr.call (Expr.typeName (Ty.fixedBytes cbSize)) [Arg.positional argExpr] =>
              -- STAGE-D #193 (bytesN cast of narrow checked arithmetic): a
              -- `bytesN(a + b)` / `bytesN(-a)` with narrow `uintN`/`intN`
              -- operands must evaluate the inner arithmetic at ITS OWN width so
              -- the checked Panic 0x11 fires (`bytes.concat(bytes1(a + b))`,
              -- `uint8 a=200,b=100` overflows before the cast), THEN convert
              -- value-preservingly into the byte lane. The int-only H2/NEG arms
              -- below stop at a `bytesN` cast target (`narrowIntCastTarget?` is
              -- `none` for `bytesN`), so mirror them here. Non-arithmetic
              -- `bytesN` casts fall through to the Direct path (byte-identical).
              let fallback := (match Expr.peelToOverflowArithmetic? argExpr with
               | some (bop, lhs, rhs) =>
                   (match Expr.binaryToCoreWithEnvTypedFuel?
                         fuel storageNames env bop lhs rhs with
                    | some (srcTy, binaryCore) =>
                        (match Ty.narrowIntCastTarget? srcTy with
                         | some _ =>
                             let checked := Ty.implicitCleanupCore srcTy binaryCore
                             (match Expr.coreAsFromTy?
                                   (Ty.bytesN cbSize) srcTy checked with
                              | some c => some c
                              | none =>
                                  Expr.toCoreAsWithEnvDirect?
                                    storageNames env targetTy expr)
                         | none =>
                             Expr.toCoreAsWithEnvDirect?
                               storageNames env targetTy expr)
                    | none =>
                        Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
               | none =>
                   (match Expr.peelToNarrowNeg? argExpr with
                    | some inner =>
                        (match Expr.abiTyWithEnv? env inner with
                         | some operandTy =>
                             (match Ty.narrowIntCastTarget? operandTy,
                                   Expr.toCoreAsWithEnvFuel?
                                     fuel storageNames env operandTy inner with
                              | some (true, _), some innerCore =>
                                  let checkedNeg :=
                                    Ty.implicitCleanupCore operandTy
                                      (SolidCore.Solidity.Source.Expr.unary
                                        SolidCore.Solidity.Source.UnaryOp.neg
                                        innerCore)
                                  (match Expr.coreAsFromTy?
                                        (Ty.bytesN cbSize) operandTy checkedNeg with
                                   | some c => some c
                                   | none =>
                                       Expr.toCoreAsWithEnvDirect?
                                         storageNames env targetTy expr)
                              | _, _ =>
                                  Expr.toCoreAsWithEnvDirect?
                                    storageNames env targetTy expr)
                         | none =>
                             Expr.toCoreAsWithEnvDirect?
                               storageNames env targetTy expr)
                    | none =>
                        Expr.toCoreAsWithEnvDirect?
                          storageNames env targetTy expr))
              -- A signedness-changing integer cast inside the bytesN cast is
              -- semantic, not an annotation wrapper.  For
              -- `bytes1(uint8(j + 1))`, peeling through `uint8` and converting
              -- the underlying `int8` arithmetic directly to bytes1 drops the
              -- explicit int-to-uint conversion and feeds an `int` value to
              -- `fixedBytesCast`, which type-mismatches.  Lower the explicit
              -- integer cast at its own type first, then convert that result to
              -- bytesN.  Other argument shapes retain the established path.
              match argExpr with
              | Expr.call (Expr.typeName argTy) [Arg.positional _] =>
                  if Ty.isIntOrUint argTy then
                    match Expr.toCoreAsWithEnvFuel?
                        fuel storageNames env argTy argExpr with
                    | some innerCore =>
                        match Expr.coreAsFromTy?
                            (Ty.bytesN cbSize) argTy innerCore with
                        | some bytesCore => some bytesCore
                        | none => fallback
                    | none => fallback
                  else
                    fallback
              | _ => fallback
          | Expr.enumFromUInt maxValue inner =>
              -- An enum conversion checks the integer expression before it checks
              -- the enum range. Preserve the expression's own integer width here:
              -- `E(a + b)` with uint8 operands must Panic(0x11) on 200 + 100,
              -- rather than first producing 300 and then Panic(0x21) as an
              -- out-of-range enum value. The direct lowering is env-less and loses
              -- that operand-width cleanup.
              (match Expr.abiTyWithEnv? env inner with
               | some sourceTy =>
                   (match Expr.toCoreAsWithEnvFuel?
                         fuel storageNames env sourceTy inner with
                    | some innerCore =>
                        some
                          (SolidCore.Solidity.Source.Expr.enumFromUInt maxValue
                            (Ty.implicitCleanupCore sourceTy innerCore))
                    | none =>
                        Expr.toCoreAsWithEnvDirect?
                          storageNames env targetTy expr)
               | none =>
                   Expr.toCoreAsWithEnvDirect?
                     storageNames env targetTy expr)
          | Expr.call (Expr.typeName castTy) [Arg.positional argExpr] =>
              -- An explicit narrow integer conversion is truncating.  First
              -- evaluate its argument at the argument's own Solidity type
              -- (which preserves any checked arithmetic inside), then apply
              -- the explicit int/uint cast.  ABI annotation commonly inserts
              -- a source-type wrapper, e.g. `uint8(a + 0)` becomes
              -- `uint8(uint256(a + uint256(0)))`; the older shape-specific
              -- peelers stopped at that wrapper and fell back to implicit
              -- `uintCleanup 8`, spuriously panicking instead of truncating.
              let explicitNarrow? : Option CoreExpr := do
                let (signed, bits) ← Ty.narrowIntCastTarget? castTy
                let sourceTy ← Expr.abiTyWithEnv? env argExpr
                let innerCore ← Expr.toCoreAsWithEnvFuel?
                  fuel storageNames env sourceTy argExpr
                some
                  (if signed then
                    SolidCore.Solidity.Source.Expr.intCast bits innerCore
                  else
                    SolidCore.Solidity.Source.Expr.uintCast bits innerCore)
              match explicitNarrow? with
              | some coreExpr => some coreExpr
              | none =>
              -- H2 (SOUNDNESS): a narrow `uintN`/`intN` explicit cast of a
              -- checked arithmetic sub-expression must evaluate that
              -- sub-expression at ITS OWN operand width (so the narrow overflow
              -- Panic 0x11 fires), then convert. The generic fallback lowers the
              -- argument through the env-less `toCore?` cast path, which drops
              -- the operands' `uintCleanup`/`intCleanup` and runs the inner
              -- add/sub/mul at 256 bits — silently wrapping instead of
              -- panicking. This covers both bare `uint8(a + b)` and, since
              -- `Small.wrap(x)` lowers to `uint8(x)`, UDVT operator-function
              -- bodies like `Small.wrap(Small.unwrap(a) + Small.unwrap(b))`.
              -- NARROW-BITAND-MASK (SOUNDNESS): a narrow `uintN`/`intN` cast whose
              -- argument is a BITWISE `&`/`|`/`^` op carrying narrow checked
              -- arithmetic (`uint8((a + b) & 255)` — the redundant cast
              -- `annotateAbi` wraps `abi.encode((a + b) & 255)` in). solc computes
              -- `a + b` at the operand width BEFORE the mask, so it Panics 0x11 on
              -- overflow; the env-less cast path drops the operand cleanup and runs
              -- it at 256 bits. Lower the bitwise op env-typed (its `_`-arm cleans
              -- each operand at the common width, firing the add's Panic) then
              -- apply the explicit (truncating) narrow cast — mirroring the
              -- overflow-arithmetic arm below. Non-bitwise arguments fall through
              -- to the unchanged arithmetic / negation / wide-cast handling.
              (match Ty.narrowIntCastTarget? castTy,
                    Expr.peelToNarrowBitwise? argExpr with
              | some (signed, bits), some (bop, lhs, rhs) =>
                  (match Expr.binaryToCoreWithEnvTypedFuel?
                      fuel storageNames env bop lhs rhs with
                   | some (srcTy, binaryCore) =>
                       let checkedBinary :=
                         Ty.implicitCleanupCore srcTy binaryCore
                       some
                         (if signed then
                           SolidCore.Solidity.Source.Expr.intCast bits checkedBinary
                         else
                           SolidCore.Solidity.Source.Expr.uintCast bits checkedBinary)
                   | none =>
                       Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
              | _, _ =>
              (match Ty.narrowIntCastTarget? castTy,
                    Expr.peelToOverflowArithmetic? argExpr with
              | some (signed, bits), some (bop, lhs, rhs) =>
                  match Expr.binaryToCoreWithEnvTypedFuel?
                      fuel storageNames env bop lhs rhs with
                  | some (srcTy, binaryCore) =>
                      -- `binaryToCoreWithEnvTyped?` returns the bare `add`/… with
                      -- cleaned operands; the checked overflow test lives in the
                      -- result cleanup (`uintCleanup`/`intCleanup`) at the
                      -- operands' own width `srcTy` — that is the Panic 0x11 the
                      -- env-less cast path dropped. The explicit narrow cast then
                      -- truncates the (checked) result to `bits`.
                      let checkedBinary :=
                        Ty.implicitCleanupCore srcTy binaryCore
                      some
                        (if signed then
                          SolidCore.Solidity.Source.Expr.intCast bits checkedBinary
                        else
                          SolidCore.Solidity.Source.Expr.uintCast bits checkedBinary)
                  | none =>
                      Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
              | _, _ =>
                  -- NEG-NARROW (cast path): an explicit narrow cast whose argument
                  -- is a unary `-x` of a narrow signed operand, e.g. `int16(-x)`.
                  -- `peelToOverflowArithmetic?` only peels binary ops, so this
                  -- shape reached the direct fallback (which negates at 256 bits
                  -- and drops the operand-width Panic 0x11). Mirror the binary cast
                  -- arm above: negate at the operand width with its checked
                  -- cleanup, then apply the EXPLICIT (truncating) cast to the cast
                  -- width. Everything else keeps the direct path.
                  (match Ty.narrowIntCastTarget? castTy,
                        Expr.peelToNarrowNeg? argExpr with
                   | some (castSigned, castBits), some inner =>
                       (match Expr.abiTyWithEnv? env inner with
                        | some operandTy =>
                            (match Ty.narrowIntCastTarget? operandTy,
                                  Expr.toCoreAsWithEnvBitAwareFuel?
                                    fuel storageNames env operandTy inner with
                             | some (true, _), some innerCore =>
                                 let checkedNeg :=
                                   Ty.implicitCleanupCore operandTy
                                     (SolidCore.Solidity.Source.Expr.unary
                                       SolidCore.Solidity.Source.UnaryOp.neg
                                       innerCore)
                                 some
                                   (if castSigned then
                                     SolidCore.Solidity.Source.Expr.intCast
                                       castBits checkedNeg
                                   else
                                     SolidCore.Solidity.Source.Expr.uintCast
                                       castBits checkedNeg)
                             | _, _ =>
                                 Expr.toCoreAsWithEnvDirect?
                                   storageNames env targetTy expr)
                        | none =>
                            Expr.toCoreAsWithEnvDirect?
                              storageNames env targetTy expr)
                   | _, _ =>
                     -- SIGNED-LITERAL-WIDE-CAST (SOUNDNESS): a WORD-width
                     -- (`uint256`/`int256`) cast whose argument mixes a RAW
                     -- untyped literal with a SIGNED operand
                     -- (`uint256(y + 10)`, `int256 y = 3`) fell through to the
                     -- env-less lowering, where the literal lowers as an
                     -- unsigned `word` while the `int` local evaluates to a
                     -- `Value.int` → interpreter typeMismatch → spurious Panic
                     -- 0x00 (solc+EVM: 13). Mirror the narrow H2/NEG arms at
                     -- the 256-bit width: lower the binary through
                     -- `binaryToCoreWithEnvTypedFuel?` (whose
                     -- `commonOperandTyWithEnv?` types the literal at the
                     -- signed common type), apply the operand-width checked
                     -- cleanup, then the explicit 256-bit cast. Gated on
                     -- `hasSignedLiteralOperandMix` so every unflagged wide
                     -- cast (`uint256(y + z)` two typed operands, unsigned
                     -- `uint256(u + 10)`, bare `uint256(y)`) keeps the
                     -- byte-identical Direct path.
                     (match
                         (match Ty.wordIntCastTarget? castTy with
                          | some castSigned =>
                              -- NARROW-ADD-WIDE-CAST (S): a WORD cast over NARROW
                              -- checked arithmetic (`uint256(a + b)`, `uint8 a,b`)
                              -- must run `a + b` at its uint8 operand width so the
                              -- overflow Panic 0x11 fires before the widening —
                              -- the same `peelToOverflowArithmeticWide?` path the
                              -- signed-literal-mix reroute uses. Both gates funnel
                              -- into the shared machinery below.
                              if Expr.hasSignedLiteralOperandMix env argExpr ||
                                  Expr.wideCastNarrowOverflowArithmetic? env argExpr ||
                                  Expr.wideCastNarrowShl? env argExpr ||
                                  (match argExpr with
                                   | Expr.assign _ _ _ => true
                                   | Expr.unary UnaryOp.preIncrement _
                                   | Expr.unary UnaryOp.preDecrement _
                                   | Expr.unary UnaryOp.postIncrement _
                                   | Expr.unary UnaryOp.postDecrement _ => true
                                   | _ => false) then
                                (match Expr.peelToOverflowArithmeticWide? argExpr with
                                | some (bop, lhs, rhs) =>
                                    (match Expr.binaryToCoreWithEnvTypedFuel?
                                          fuel storageNames env bop lhs rhs with
                                     | some (srcTy, binaryCore) =>
                                         let checkedBinary :=
                                           Ty.implicitCleanupCore srcTy binaryCore
                                         some
                                           (if castSigned then
                                             SolidCore.Solidity.Source.Expr.intCast
                                               256 checkedBinary
                                           else
                                             SolidCore.Solidity.Source.Expr.uintCast
                                               256 checkedBinary)
                                     | none => none)
                                | none =>
                                    (match Expr.peelToNegWide? argExpr with
                                    | some inner =>
                                        (match Expr.abiTyWithEnv? env inner with
                                         | some operandTy =>
                                             (match operandTy,
                                                   Expr.toCoreAsWithEnvBitAwareFuel?
                                                     fuel storageNames env
                                                     operandTy inner with
                                              | Ty.int _, some innerCore =>
                                                  let checkedNeg :=
                                                    Ty.implicitCleanupCore operandTy
                                                      (SolidCore.Solidity.Source.Expr.unary
                                                        SolidCore.Solidity.Source.UnaryOp.neg
                                                        innerCore)
                                                  some
                                                    (if castSigned then
                                                      SolidCore.Solidity.Source.Expr.intCast
                                                        256 checkedNeg
                                                    else
                                                      SolidCore.Solidity.Source.Expr.uintCast
                                                        256 checkedNeg)
                                              | _, _ => none)
                                         | none => none)
                                    | none =>
                                        -- Nested-cast shape: `annotateAbi`
                                        -- wraps the conversion argument at the
                                        -- ARGUMENT'S own type, so a NARROW
                                        -- operand yields `int256(int128(y+10))`
                                        -- — the wide peeler must NOT strip the
                                        -- (truncating) narrow cast. Lower the
                                        -- argument at ITS OWN type through the
                                        -- env-aware recursion (whose narrow H2
                                        -- arm checks `y + 10` at int128 and
                                        -- applies the int128 cast), then apply
                                        -- the explicit 256-bit conversion.
                                        (match Expr.abiTyWithEnv? env argExpr with
                                         | some srcTy =>
                                             (match
                                                 Expr.toCoreAsWithEnvBitAwareFuel?
                                                   fuel storageNames env
                                                   srcTy argExpr with
                                              | some innerCore =>
                                                  some
                                                    (if castSigned then
                                                      SolidCore.Solidity.Source.Expr.intCast
                                                        256 innerCore
                                                    else
                                                      SolidCore.Solidity.Source.Expr.uintCast
                                                        256 innerCore)
                                              | none => none)
                                         | none => none)))
                              else none
                          | none => none) with
                      | some coreExpr => some coreExpr
                      | none =>
                       -- #201 (B/F, cast-of-builtin): an explicit cast whose
                       -- ARGUMENT needs the env-aware operand-width cleanup
                       -- (`Expr.abiArgNeedsEnvCleanup?`) must lower that argument
                       -- env-aware so its Panic 0x11 fires, then convert exactly
                       -- as the implicit widening does (`coreAsFromTy?` through the
                       -- cast type, then to the target). This covers the direct
                       -- builtin case (`uint256(keccak256(abi.encode(a + b)))`,
                       -- `uint8 a,b`) AND — via the transparent-cast recursion in
                       -- `abiArgNeedsEnvCleanup?` — a flagged builtin/arithmetic
                       -- under a NARROW-cast tower (`uint128(uint128(addmod(
                       -- uint256(a + b), 1, 7)))`, the arg shape a value returned
                       -- through an internal function pointer takes): each cast
                       -- layer re-enters here and peels inward until the innermost
                       -- flagged arm fires the cleanup. Unflagged casts keep the
                       -- byte-identical Direct path.
                       (match (if Expr.abiArgNeedsEnvCleanup? argExpr then
                           (do
                             let srcTy ← Expr.abiTyWithEnv? env argExpr
                             let innerCore ←
                               Expr.toCoreAsWithEnvFuel?
                                 fuel storageNames env srcTy argExpr
                             let casted ←
                               match castTy, srcTy with
                               -- `address(uint160(e))` is represented by the
                               -- already-converted 160-bit word.  This explicit
                               -- conversion is value-preserving at the core
                               -- level, but `coreAsFromTy?` intentionally only
                               -- models implicit conversions and therefore
                               -- declines it.  Keep the env-aware lowering of
                               -- `e` so narrow checked arithmetic still Panics
                               -- before the address conversion.
                               | Ty.address _, Ty.uint 160 => some innerCore
                               | _, _ =>
                                   Expr.coreAsFromTy? castTy srcTy innerCore
                             Expr.coreAsFromTy? targetTy castTy casted)
                         else none) with
                       | some coreExpr => some coreExpr
                       | none =>
                           Expr.toCoreAsWithEnvDirect?
                             storageNames env targetTy expr)))))
          | Expr.ternary cond thenExpr elseExpr => do
              let condCore ←
                Expr.toCoreAsWithEnvFuel? fuel storageNames env Ty.bool cond
              let thenCore ←
                Expr.toCoreAsWithEnvFuel? fuel storageNames env targetTy thenExpr
              let elseCore ←
                Expr.toCoreAsWithEnvFuel? fuel storageNames env targetTy elseExpr
              some
                (SolidCore.Solidity.Source.Expr.ternary
                  condCore thenCore elseCore)
          | Expr.binary op lhs rhs =>
              -- NARROW-ARITH-UNDER-SHIFT (SOUNDNESS): a `<<`/`>>` whose shifted
              -- value OR shift count carries narrow checked arithmetic must
              -- evaluate that subtree at its own operand width, so overflow
              -- Panics 0x11 before the shift. This includes both
              -- `(a * b) << k` and `x << (a + b)`.
              -- `binaryToCoreWithEnvTypedFuel?` declines shifts (`shl/shr =>
              -- none`), so the whole shift subtree otherwise falls to the env-less
              -- Direct path, which lowers the inner `mul`/`add` to a bare 256-bit
              -- op with NO `implicitCleanupCore` — silently wrapping (`2^32 *
              -- 2^32 = 2^64` fits in 256 bits, `((a*b) << 0) != 0` reads false)
              -- instead of panicking. Re-lower only flagged operands env-aware;
              -- unflagged operands retain the byte-identical Direct path.
              -- A `bytesN`-target shift is intercepted earlier by the fixed-bytes
              -- bit-op arm, whose fuel-aware variant applies the same rule.
              match
                  (match op with
                   | BinaryOp.shl | BinaryOp.shr =>
                       let lhsNeeds := Expr.abiArgNeedsEnvCleanup? lhs
                       let rhsNeeds := Expr.abiArgNeedsEnvCleanup? rhs
                       if lhsNeeds || rhsNeeds then do
                         let coreOp ← BinaryOp.toCore? op
                         let lhsCore ←
                           if lhsNeeds then do
                             let lhsTy ← Expr.abiTyWithEnv? env lhs
                             Expr.toCoreAsWithEnvFuel?
                               fuel storageNames env lhsTy lhs
                           else
                             Expr.toCore? storageNames lhs
                         let rhsCore ←
                           if rhsNeeds then do
                             let rhsTy ← Expr.abiTyWithEnv? env rhs
                             Expr.toCoreAsWithEnvFuel?
                               fuel storageNames env rhsTy rhs
                           else
                             Expr.toCore? storageNames rhs
                         let shiftTy ← Expr.abiTyWithEnv? env expr
                         Expr.coreAsFromTy? targetTy shiftTy
                           (SolidCore.Solidity.Source.Expr.binary
                             coreOp lhsCore rhsCore)
                       else none
                   | _ => none) with
              | some coreExpr => some coreExpr
              | none =>
              match
                  Expr.binaryToCoreWithEnvTypedFuel?
                    fuel storageNames env op lhs rhs with
              | some (sourceTy, coreExpr) =>
                  -- SOUNDNESS (narrow-arithmetic-widened gap, recorded in the
                  -- G15 note): solc computes a binary arithmetic op at the
                  -- operands' common type REGARDLESS of a wider assignment /
                  -- return / argument target, so a narrow overflow Panics 0x11
                  -- even when the result is widened afterwards (`uint16 c =
                  -- uint8a + uint8b` with `a+b > 255` panics, not 300).
                  -- `binaryToCoreWithEnvTyped?` returns the bare op; its checked
                  -- cleanup lives at the operand width `sourceTy`. `coreAsFromTy?`
                  -- for a WIDER target applies only the target-width cleanup
                  -- (which never catches the operand overflow), so the operand
                  -- cleanup must be applied here first. (Same-width targets
                  -- already clean in `coreAsFromTy?`; the extra cleanup is then
                  -- idempotent. Only overflow-arithmetic ops need it — comparisons
                  -- and bitwise ops never overflow their operand width.)
                  let coreExpr :=
                    if BinaryOp.isOverflowArithmetic op then
                      Ty.implicitCleanupCore sourceTy coreExpr
                    else
                      coreExpr
                  Expr.coreAsFromTy? targetTy sourceTy coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
          | Expr.unary UnaryOp.neg inner =>
              -- NEG-NARROW (SOUNDNESS): unary `-x` of a narrow (`N < 256`) signed
              -- operand is evaluated by solc at the OPERAND width
              -- (`negate_t_intN`), which in a checked context Panics 0x11 when x is
              -- `type(intN).min`, BEFORE any implicit widening to a wider
              -- return/assignment/argument target. This is the unary analogue of
              -- the binary `isOverflowArithmetic` path just above: lower the
              -- operand at its own width, negate, apply the operand-width checked
              -- cleanup (the Panic 0x11 in a checked block, the wrap to `intN.min`
              -- in an `unchecked` block — the `intCleanup` node decides at runtime),
              -- and only then widen via `coreAsFromTy?`. Non-narrow (`int256`)
              -- operands fall through unchanged (`checkedSignedNeg` already checks
              -- at full width), as do unsigned operands (unary minus on an unsigned
              -- integer is a type error) and negative number literals (`-5` is not
              -- narrow-typed), all of which keep the existing direct path.
              -- SIGNED-LITERAL-WIDE-CAST (SOUNDNESS): ALSO reroute a WORD-width
              -- (`int256`) signed negation whose operand mixes a RAW untyped
              -- literal with a signed operand (`-(y * 2)`, `-(y - z * 2)` with
              -- `int256 y, z`) — the Direct/env-less fallback lowers the
              -- literal as an unsigned `word` against the `Value.int` local →
              -- interpreter typeMismatch → spurious Panic 0x00 (solc+EVM
              -- compute the real value). The env-aware operand lowering types
              -- the literal at the signed common type; the operand-width
              -- checked cleanup (`intCleanup 256`) keeps the -(int256.min)
              -- Panic 0x11 exactly as `checkedSignedNeg` did. Unflagged wide
              -- negations (`-(y - z)`, no literal) keep the byte-identical
              -- Direct path.
              (match Expr.abiTyWithEnv? env inner with
               | some operandTy =>
                   let reroute :=
                     match Ty.narrowIntCastTarget? operandTy with
                     | some (true, _) => true
                     | some _ => false
                     | none =>
                         match Ty.wordIntCastTarget? operandTy with
                         | some true => Expr.hasSignedLiteralOperandMix env inner
                         | _ => false
                   (match (if reroute then
                         Expr.toCoreAsWithEnvFuel?
                           fuel storageNames env operandTy inner
                       else none) with
                    | some innerCore =>
                        let checkedNeg :=
                          Ty.implicitCleanupCore operandTy
                            (SolidCore.Solidity.Source.Expr.unary
                              SolidCore.Solidity.Source.UnaryOp.neg innerCore)
                        Expr.coreAsFromTy? targetTy operandTy checkedNeg
                    | none =>
                        Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
               | none =>
                   Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.unary UnaryOp.bitNot inner =>
              -- A narrow bitwise NOT is evaluated at its operand type. Besides
              -- masking the final `~` to that width, its operand must retain
              -- any checked arithmetic cleanup: `~(a + b)` with `uint8`
              -- operands Panics 0x11 on the addition before the complement.
              -- The prior env-aware reroute reached this node but then fell
              -- through to the env-less direct lowerer, which evaluated the
              -- addition at 256 bits. Lower the operand recursively at its own
              -- type, apply the existing truncating bit-not cleanup, and only
              -- then convert to the surrounding target type.
              (match Expr.abiTyWithEnv? env inner with
               | some operandTy =>
                   (match Ty.narrowIntCastTarget? operandTy with
                    | some _ =>
                        (match Expr.toCoreAsWithEnvFuel?
                            fuel storageNames env operandTy inner with
                         | some innerCore =>
                             let cleanedNot :=
                               Ty.implicitCleanupCore operandTy
                                 (SolidCore.Solidity.Source.Expr.unary
                                   SolidCore.Solidity.Source.UnaryOp.bitNot
                                   innerCore)
                             Expr.coreAsFromTy? targetTy operandTy cleanedNot
                         | none =>
                             Expr.toCoreAsWithEnvDirect?
                               storageNames env targetTy expr)
                    | none =>
                        Expr.toCoreAsWithEnvDirect?
                          storageNames env targetTy expr)
               | none =>
                   Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.unary UnaryOp.logicalNot inner =>
              -- R2 (Stage B): `!c` in a bool-typed position recurses on the
              -- operand at `Ty.bool` through the FULL env-aware lowering, so a
              -- comparison under `!` keeps the operand-width checked cleanup
              -- (`if (!((a + b) < n))` with `uint8 a,b` must Panic 0x11 —
              -- previously the whole `!` subtree fell to the env-less
              -- `toCore?`, dropping it). Non-bool targets keep the direct path.
              if targetTy == Ty.bool then
                match Expr.toCoreAsWithEnvFuel?
                    fuel storageNames env Ty.bool inner with
                | some innerCore =>
                    some
                      (SolidCore.Solidity.Source.Expr.unary
                        SolidCore.Solidity.Source.UnaryOp.logicalNot innerCore)
                | none =>
                    Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
              else
                Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
          | Expr.index base key =>
              -- R2 (Stage B, index-key cleanup): a NARROW (`uintN`/`intN`,
              -- N < 256) index key is evaluated by solc at ITS OWN type — a
              -- checked arithmetic key (`arr[a + b]`, `uint8 a,b`) Panics 0x11
              -- on overflow BEFORE the (implicit, value-preserving) widening
              -- to the index/lookup width. The env-less index lowering ran the
              -- key bare at 256 bits. Reroute ONLY narrow-typed keys (wide
              -- keys already check at full width in core arithmetic), building
              -- the read with `indexReadCoreBuilder?` (the exact `toCore?`
              -- index shapes) and the key through the full env-aware lowering.
              (match
                  (do
                    let keyTy ← Expr.abiTyWithEnv? env key
                    -- WS1 (H): ALSO reroute a WIDE key whose SUBTREE is
                    -- flagged (`arr[arr[a + b]]` — the outer uint256 key
                    -- contains a narrow checked add); the env-aware recursion
                    -- reaches the inner narrow key. NESTED-MAPPING-KEY (S):
                    -- ALSO reroute when the BASE subtree is flagged
                    -- (`m[a + b][0]` — the narrow checked add is the INNER
                    -- mapping key of a nested read, `uint8 a,b`); the env-less
                    -- `indexReadCoreBuilder?` lowered the base via `toCore?`, so
                    -- the inner key ran at 256 bits and its Panic 0x11 was lost.
                    -- Unflagged wide keys/bases keep the env-less path
                    -- byte-identically.
                    let _ ←
                      (if (Ty.narrowIntCastTarget? keyTy).isSome ||
                          Expr.abiArgNeedsEnvCleanup? key ||
                          Expr.abiArgNeedsEnvCleanup? base then
                        some ()
                      else
                        none)
                    let keyCore ←
                      Expr.toCoreAsWithEnvFuel? fuel storageNames env keyTy key
                    -- Build the read. If the BASE subtree itself needs the
                    -- operand-width cleanup (a nested narrow index key,
                    -- `m[a + b][0]`), lower the base through the FULL env-aware
                    -- recursion so its inner narrow key Panics 0x11; the outer
                    -- read is the general `index`/`fixedBytesIndex` over that
                    -- base value. Otherwise keep the exact env-less
                    -- `indexReadCoreBuilder?` shapes (state-var `storageIndex`,
                    -- `fixedBytesIndex`, general `index`) byte-identically.
                    let readCore ←
                      (if Expr.abiArgNeedsEnvCleanup? base then
                        (do
                          let baseTy ← Expr.abiTyWithEnv? env base
                          let baseCore ←
                            Expr.toCoreAsWithEnvFuel? fuel storageNames env
                              baseTy base
                          match Ty.fixedBytesSize? baseTy with
                          | some size =>
                              some
                                (SolidCore.Solidity.Source.Expr.fixedBytesIndex
                                  size baseCore keyCore)
                          | none =>
                              some
                                (SolidCore.Solidity.Source.Expr.index baseCore
                                  keyCore))
                      else
                        (do
                          let buildRead ←
                            Expr.indexReadCoreBuilder? storageNames base
                          some (buildRead keyCore)))
                    let sourceTy ← Expr.abiTyWithEnv? env (Expr.index base key)
                    Expr.coreAsFromTy? targetTy sourceTy readCore) with
              | some coreExpr => some coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.literal (Literal.number text) =>
              -- Stage C: a function identifier in value position was rewritten
              -- to its dispatch-ID literal (`rewriteInternalFnValueIdents`);
              -- in an internal-fn-typed context it becomes the core
              -- internal-function-pointer literal. (A REAL number literal in an
              -- internal-fn-typed position is rejected by the typechecker, so
              -- post-typecheck this shape is unambiguous.) External-fn-typed
              -- and ordinary contexts keep the existing path.
              (match targetTy with
              | Ty.functionWithLocations _ _ _ _ _ Visibility.external_ =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
              | Ty.functionWithLocations _ _ _ _ _ _ =>
                  (parseNumberNat? text).map
                    SolidCore.Solidity.Source.Expr.internalFunction
              | _ =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.member (Expr.ident "abi") "encode") args =>
              -- STAGE-D #193: route EVERY `abi.encode` argument through the
              -- env-aware helper. TC1 `bytesN`-common-type conditionals keep the
              -- per-branch widening; a narrow-checked-arithmetic argument gets
              -- its operand-width Panic 0x11 (`abi.encode(a + b)`, `uint8`); any
              -- other argument is byte-identical (env-less). `none` (a shape the
              -- env-less path also declined) falls back to Direct.
              (match Args.toAbiEncodeWithEnvFuel? fuel storageNames env args with
               | some (tys, exprs) =>
                   some
                     (SolidCore.Solidity.Source.Expr.abiEncode tys
                       exprs)
               | none =>
                   Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.member (Expr.ident "abi") "decode")
              [Arg.positional data, Arg.positional typesExpr] =>
              -- `abi.decode` consumes its data expression by value. Preserve
              -- the data subtree's own integer width before decoding, e.g.
              -- `abi.decode(abi.encode(a + b), ...)` with `uint8 a,b` must
              -- Panic 0x11 while constructing the bytes.
              (match (if Expr.abiArgNeedsEnvCleanup? data then
                  (do
                    let (tys, cleanups, _) ←
                      Expr.toAbiDecode? storageNames data typesExpr
                    let dataTy ← Expr.abiTyWithEnv? env data
                    let dataCore ←
                      Expr.toCoreAsWithEnvFuel?
                        fuel storageNames env dataTy data
                    some
                      (SolidCore.Solidity.Source.Expr.abiDecode
                        tys cleanups dataCore))
                else none) with
              | some coreExpr => some coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.member (Expr.ident "abi") "encodePacked") args =>
              (match Args.toAbiEncodeSourceWithEnvFuel? fuel storageNames env args with
               | some (sourceTys, coreTys, exprs) =>
                   some (SolidCore.Solidity.Source.Expr.abiEncodePacked
                     (Tys.packedTopWidths sourceTys) coreTys
                     exprs)
               | none =>
                   Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector")
              (Arg.positional selector :: args) =>
              -- Selector lowered exactly as the env-less arm (#143); the
              -- following arguments env-aware (#193).
              (match (do
                  let selectorCore ←
                    match Expr.abiTy? storageNames selector with
                    | some (Ty.bytesN 4) => Expr.toCore? storageNames selector
                    | some (Ty.fixedBytes 4) => Expr.toCore? storageNames selector
                    | _ => Expr.toCoreFixedBytesLiteralAs? (Ty.fixedBytes 4) selector
                  let (tys, exprs) ←
                    Args.toAbiEncodeWithEnvFuel? fuel storageNames env args
                  some
                    (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
                      selectorCore tys exprs)) with
               | some coreExpr => some coreExpr
               | none => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSignature")
              (Arg.positional (Expr.literal (Literal.string signature)) :: args) =>
              (match Args.toAbiEncodeWithEnvFuel? fuel storageNames env args with
               | some (tys, exprs) =>
                   some
                     (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
                       (SolidCore.Solidity.Source.Expr.word
                         (SolidCore.Solidity.Source.ABI.selectorFromSignature
                           signature))
                       tys exprs)
               | none => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
              [Arg.positional functionPointer, Arg.positional (Expr.tuple items)] =>
              (match (do
                  let (sourceTys, coreTys, coreExprs) ←
                    TupleItems.toAbiEncodeSourceWithEnvFuel? fuel storageNames env items
                  let selectorCore ←
                    Expr.functionPointerSelectorCore?
                      storageNames functionPointer sourceTys
                  some
                    (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
                      selectorCore coreTys
                      coreExprs)) with
               | some coreExpr => some coreExpr
               | none => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          -- A one-parameter encodeCall is imported as a plain expression,
          -- not a singleton tuple. Preserve its operand-width checks too.
          | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
              [Arg.positional functionPointer, Arg.positional argumentExpr] =>
              (match (do
                  let (sourceTy, coreTy, coreExpr) ←
                    Expr.toAbiEncodeSourceArgWithEnvFuel? fuel storageNames env argumentExpr
                  let selectorCore ←
                    Expr.functionPointerSelectorCore?
                      storageNames functionPointer [sourceTy]
                  some
                    (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
                      selectorCore [coreTy] [coreExpr])) with
               | some coreExpr => some coreExpr
               | none => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.ident "keccak256") [Arg.positional bytes] =>
              -- STAGE-D #193: lower the hashed bytes env-aware so a nested
              -- `abi.encode*`/`concat` argument keeps its operand-width cleanup
              -- (`keccak256(abi.encodePacked(a + b))`, `uint8`).
              (match Expr.toCoreAsWithEnvFuel? fuel storageNames env Ty.bytes bytes with
               | some bytesCore =>
                   some
                     (SolidCore.Solidity.Source.Expr.keccak256
                       bytesCore)
               | none => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.ident "sha256") [Arg.positional bytes] =>
              (match Expr.toCoreAsWithEnvFuel? fuel storageNames env Ty.bytes bytes with
               | some bytesCore =>
                   some
                     (SolidCore.Solidity.Source.Expr.externalHash
                       SolidCore.Solidity.Source.ExternalHashKind.sha256
                       bytesCore)
               | none => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.ident "ripemd160") [Arg.positional bytes] =>
              (match Expr.toCoreAsWithEnvFuel? fuel storageNames env Ty.bytes bytes with
               | some bytesCore =>
                   -- `ripemd160` is `bytesN 20`. When the result flows to a WIDER
                   -- `bytesN` target (e.g. an implicit `bytes20 -> bytes32` return),
                   -- solc inserts `convert_t_bytesM_to_t_bytesN`; because `bytesN`
                   -- is left-aligned that widening moves the 20-byte digest into the
                   -- HIGH bytes (`0x9c11..8d31000..0`). Applying the same
                   -- `coreAsFromTy?` the generic Direct path uses restores the
                   -- widening cast this special arm otherwise drops (leaving the
                   -- digest right-aligned -> wrong value). Identity for a `bytes20`
                   -- target; falls back to the bare hash if no conversion applies.
                   let hashCore :=
                     SolidCore.Solidity.Source.Expr.externalHash
                       SolidCore.Solidity.Source.ExternalHashKind.ripemd160
                       bytesCore
                   (match Expr.coreAsFromTy? targetTy (Ty.bytesN 20) hashCore with
                    | some coreExpr => some coreExpr
                    | none => some hashCore)
               | none => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.ident "ecrecover")
              [ Arg.positional digest
              , Arg.positional v
              , Arg.positional r
              , Arg.positional s ] =>
              -- Each precompile argument is evaluated at its source type
              -- before it is packed into the 128-byte input. The direct arm
              -- lowered all four env-less, losing checks such as `uint8 a+b`
              -- in the `v` position.
              (match (if [digest, v, r, s].any Expr.abiArgNeedsEnvCleanup? then
                  (do
                    let lower := fun e => do
                      let ty ← Expr.abiTyWithEnv? env e
                      Expr.toCoreAsWithEnvFuel? fuel storageNames env ty e
                    let digestCore ← lower digest
                    let vCore ← lower v
                    let rCore ← lower r
                    let sCore ← lower s
                    some
                      (SolidCore.Solidity.Source.Expr.ecrecover
                        digestCore vCore rCore sCore))
                else none) with
              | some coreExpr => some coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.member (Expr.ident "bytes") "concat") args
          | Expr.call (Expr.member (Expr.typeName Ty.bytes) "concat") args
          | Expr.call (Expr.member (Expr.ident "string") "concat") args
          | Expr.call (Expr.member (Expr.typeName Ty.string) "concat") args =>
              -- STAGE-D #193: `bytes.concat`/`string.concat` env-aware args, but
              -- keep the exact env-less acceptance gate (`allBytesConcatArgs`).
              (match Args.toAbiEncodeSourceWithEnvFuel? fuel storageNames env args with
               | some (sourceTys, coreTys, coreExprs) =>
                   if Tys.allBytesConcatArgs sourceTys then
                     some (SolidCore.Solidity.Source.Expr.abiEncodePacked
                       (Tys.packedTopWidths sourceTys) coreTys
                       coreExprs)
                   else
                     Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
               | none => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.member base "length" =>
              -- #201 (C): `.length` OF an expression carrying narrow checked
              -- arithmetic must evaluate its base env-aware so the
              -- operand-width Panic 0x11 fires. This includes abi/hash/concat
              -- builtins and indexed memory elements such as
              -- `values[a + b].length`; the Direct fallback lowered the whole
              -- `.length` subtree env-less. Result type is `uint 256` exactly
              -- as `Expr.abiTyWithEnv?` types `.length`. Every unflagged
              -- `.length` keeps the byte-identical Direct path.
              (match (if Expr.abiArgNeedsEnvCleanup? base then
                  (do
                    let baseTy ← Expr.abiTyWithEnv? env base
                    let baseCore ←
                      Expr.toCoreAsWithEnvFuel? fuel storageNames env baseTy base
                    Expr.coreAsFromTy? targetTy (Ty.uint 256)
                      (SolidCore.Solidity.Source.Expr.length baseCore))
                else none) with
              | some coreExpr => some coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.member base member =>
              -- Account-member receivers are value-use boundaries too. Keep
              -- a nested operand-width check while forming the address before
              -- reading its balance/code/codehash.
              (match (if (member == "balance" || member == "code" ||
                      member == "codehash") &&
                    Expr.abiArgNeedsEnvCleanup? base then
                  (do
                    let baseTy ← Expr.abiTyWithEnv? env base
                    let baseCore ←
                      Expr.toCoreAsWithEnvFuel?
                        fuel storageNames env baseTy base
                    if member == "balance" then
                      some
                        (SolidCore.Solidity.Source.Expr.envLookup
                          SolidCore.Solidity.Source.EnvLookup.accountBalance
                          baseCore)
                    else if member == "code" then
                      some
                        (SolidCore.Solidity.Source.Expr.envBytesLookup
                          SolidCore.Solidity.Source.EnvBytesLookup.accountCode
                          baseCore)
                    else
                      some
                        (SolidCore.Solidity.Source.Expr.envLookup
                          SolidCore.Solidity.Source.EnvLookup.accountCodehash
                          baseCore))
                else none) with
              | some coreExpr => some coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.call (Expr.ident amName)
              [Arg.positional amX, Arg.positional amY, Arg.positional amM] =>
              -- WS1 (H, addmod/mulmod): a builtin-modular-arithmetic argument
              -- carrying narrow checked arithmetic (`addmod(a + b, 1, 7)`,
              -- `uint8 a,b`) evaluates at its OWN width first — solc emits the
              -- checked uint8 add (Panic 0x11 on 300) BEFORE the 512-bit
              -- modular op; the env-less lowering ran the add bare at 256 bits
              -- (returning (300+1)%7). Only flagged args reroute; every other
              -- addmod/mulmod (and every non-addmod 3-arg call) keeps the
              -- byte-identical Direct path.
              (match (if (amName == "addmod" || amName == "mulmod") &&
                    (Expr.abiArgNeedsEnvCleanup? amX ||
                      Expr.abiArgNeedsEnvCleanup? amY ||
                      Expr.abiArgNeedsEnvCleanup? amM) then
                  (do
                    let xTy ← Expr.abiTyWithEnv? env amX
                    let yTy ← Expr.abiTyWithEnv? env amY
                    let mTy ← Expr.abiTyWithEnv? env amM
                    let xCore ←
                      Expr.toCoreAsWithEnvFuel? fuel storageNames env xTy amX
                    let yCore ←
                      Expr.toCoreAsWithEnvFuel? fuel storageNames env yTy amY
                    let mCore ←
                      Expr.toCoreAsWithEnvFuel? fuel storageNames env mTy amM
                    let callCore :=
                      if amName == "addmod" then
                        SolidCore.Solidity.Source.Expr.addMod xCore yCore mCore
                      else
                        SolidCore.Solidity.Source.Expr.mulMod xCore yCore mCore
                    Expr.coreAsFromTy? targetTy (Ty.uint 256) callCore)
                else none) with
              | some coreExpr => some coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.newExpr newTy [Arg.positional lengthExpr] =>
              -- WS1 (H, new-array/bytes size): `new uint256[](a + b)` with
              -- `uint8 a,b` — solc evaluates the length at ITS OWN type
              -- (checked uint8 add, Panic 0x11 on 300) before the allocation;
              -- the env-less lowering ran the add bare at 256 bits and
              -- allocated 300 elements. Only flagged lengths reroute; contract
              -- creation (`new C(x)`) and unflagged lengths keep the
              -- byte-identical Direct path.
              (match (if Expr.abiArgNeedsEnvCleanup? lengthExpr then
                  (do
                    let lenTy ← Expr.abiTyWithEnv? env lengthExpr
                    let lenCore ←
                      Expr.toCoreAsWithEnvFuel?
                        fuel storageNames env lenTy lengthExpr
                    match newTy with
                    | Ty.bytes =>
                        some (SolidCore.Solidity.Source.Expr.newBytes lenCore)
                    | Ty.string =>
                        some (SolidCore.Solidity.Source.Expr.newBytes lenCore)
                    | Ty.array elementTy none => do
                        let coreElementTy ← Ty.toCore? elementTy
                        some
                          (SolidCore.Solidity.Source.Expr.newDynamicArray
                            coreElementTy lenCore)
                    | _ => none)
                else none) with
              | some coreExpr => some coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.slice base start stop =>
              -- WS1 (H, calldata-slice bounds): `msg.data[a + b:]` with
              -- `uint8 a,b` — solc evaluates each slice bound at ITS OWN type
              -- (checked uint8 add, Panic 0x11 on 300) before the slice bounds
              -- check; the env-less lowering (the only slice arm, in
              -- `Expr.toCore?`) ran the add bare at 256 bits and then failed
              -- the bounds check with an EMPTY revert — wrong revert kind.
              -- Mirror the `new T[](len)` arm above: only flagged bounds
              -- reroute (each lowered env-aware at its own type); unflagged
              -- slices keep the byte-identical Direct path. Covers `[lo:hi]`,
              -- `[lo:]`, and `[:hi]`.
              (match (if start.any Expr.abiArgNeedsEnvCleanup? ||
                    stop.any Expr.abiArgNeedsEnvCleanup? then
                  (do
                    let baseCore ← Expr.toCore? storageNames base
                    let startCore? ←
                      match start with
                      | some boundExpr => do
                          let boundTy ← Expr.abiTyWithEnv? env boundExpr
                          let core ←
                            Expr.toCoreAsWithEnvFuel?
                              fuel storageNames env boundTy boundExpr
                          some (some core)
                      | none => some none
                    let stopCore? ←
                      match stop with
                      | some boundExpr => do
                          let boundTy ← Expr.abiTyWithEnv? env boundExpr
                          let core ←
                            Expr.toCoreAsWithEnvFuel?
                              fuel storageNames env boundTy boundExpr
                          some (some core)
                      | none => some none
                    let sourceTy ← Expr.abiTyWithEnv? env expr
                    Expr.coreAsFromTy? targetTy sourceTy
                      (SolidCore.Solidity.Source.Expr.slice
                        baseCore startCore? stopCore?))
                else none) with
              | some coreExpr => some coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.tuple items =>
              -- STRUCT-FIELD-UNDER-ABI: `resolveStructs` represents a struct
              -- constructor as a tuple of field-typed casts.  Once a flagged
              -- tuple reaches the env-aware ABI path, lower every field at its
              -- declared type so nested narrow checked arithmetic is evaluated
              -- before the field cast.
              (match targetTy with
               | Ty.struct _ fieldTys
               | Ty.tuple fieldTys =>
                   match TupleItems.toCoreAsListWithEnvFuel?
                       fuel storageNames env fieldTys items with
                   | some coreExprs =>
                       some (SolidCore.Solidity.Source.Expr.tuple coreExprs)
                   | none =>
                       Expr.toCoreAsWithEnvDirect?
                         storageNames env targetTy expr
               | _ =>
                   Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.array elems =>
              -- WS1 (H, inline array literal): `uint8[2] memory t = [a + b, 1]`
              -- fell entirely to the env-less AL-EXEC arm, whose per-element
              -- `toCoreAs?` cannot lower narrow checked arithmetic — the whole
              -- statement OVER-REJECTED (and the Panic 0x11 was unreachable).
              -- Lower each element through the full env-aware recursion at the
              -- AL1-verified target element type (left-to-right, exactly the
              -- AL-EXEC order); raw literals still constant-fold via the
              -- recursion's literal routing. Declines (Direct) for non-array
              -- targets and length mismatches, so every previously-accepted
              -- literal keeps its lowering.
              (match targetTy with
               | Ty.array elemTy (some n) =>
                   if elems.length == n then
                     match
                         Exprs.toCoreAsListWithEnvFuel?
                           fuel storageNames env elemTy elems with
                     | some coreExprs =>
                         some
                           (SolidCore.Solidity.Source.Expr.fixedArray coreExprs)
                     | none =>
                         Expr.toCoreAsWithEnvDirect?
                           storageNames env targetTy expr
                   else
                     Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
               | _ =>
                   Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | Expr.payableConversion inner =>
              -- Payability changes the static address type, not the runtime
              -- word. Recurse through the wrapper so checked arithmetic inside
              -- `payable(address(uint160(a + b)))` is still evaluated at the
              -- operands' width.
              (match (if Expr.abiArgNeedsEnvCleanup? inner then
                  (do
                    let innerTy ← Expr.abiTyWithEnv? env inner
                    Expr.toCoreAsWithEnvFuel?
                      fuel storageNames env innerTy inner)
                else none) with
              | some coreExpr => some coreExpr
              | none =>
                  Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr)
          | _ =>
              Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr

/-- WS1 (H, inline array literal): element list of an inline array literal,
    each element lowered through the full env-aware recursion at the target
    element type (left-to-right). Fuel 0 degrades to the env-less AL-EXEC
    element lowering (`Expr.arrayLiteralCoreExprsAs?`) — never a new reject. -/
def Exprs.toCoreAsListWithEnvFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) (elemTy : Ty) : List Expr -> Option (List CoreExpr)
  | [] => some []
  | expr :: rest =>
      match fuel with
      | 0 => Expr.arrayLiteralCoreExprsAs? storageNames elemTy (expr :: rest)
      | Nat.succ fuel => do
          let coreExpr ←
            Expr.toCoreAsWithEnvFuel? fuel storageNames env elemTy expr
          let coreExprs ←
            Exprs.toCoreAsListWithEnvFuel? fuel storageNames env elemTy rest
          some (coreExpr :: coreExprs)

/-- Env-aware counterpart of tuple/struct field lowering. -/
def TupleItems.toCoreAsListWithEnvFuel? (fuel : Nat)
    (storageNames : List Name) (env : TypeEnv) :
    List Ty → List TupleItem → Option (List CoreExpr)
  | [], [] => some []
  | targetTy :: targetTys, TupleItem.value expr :: rest =>
      match fuel with
      | 0 => none
      | Nat.succ fuel => do
          let coreExpr ←
            Expr.toCoreAsWithEnvFuel? fuel storageNames env targetTy expr
          let coreExprs ←
            TupleItems.toCoreAsListWithEnvFuel?
              fuel storageNames env targetTys rest
          some (coreExpr :: coreExprs)
  | _, _ => none

/-- ITEM-1 (array-literal over-rejection): env-aware type of ONE inline
    array-literal element. The env-less `Expr.abiTy?` has no identifier arm,
    so `[storageBytes, other]` / `[storageLocal, …]` could never compute a
    common element type and the whole statement over-rejected even though
    the normalizer + runtime materializer handle the lowered shape. Elements
    type through `Expr.abiTyWithEnv?` (which sees state variables and
    storage locals); a nested array literal recurses. -/
def Expr.arrayLiteralElemTyWithEnvFuel? (fuel : Nat) (env : TypeEnv)
    (expr : Expr) : Option Ty :=
  match fuel with
  | 0 => none
  | Nat.succ fuel =>
      match expr with
      | Expr.array elems => do
          let elemTy ← Exprs.arrayLiteralCommonTyWithEnvFuel? fuel env elems
          some (Ty.array elemTy (some elems.length))
      | _ => Expr.abiTyWithEnv? env expr

/-- ITEM-1: env-aware common (mobile) element type of an inline array
    literal — the with-env twin of `Expr.arrayLiteralCommonTy?`, combining
    element types with the SAME `arrayLiteralCommonInfo?` literal/mobile
    rules. -/
def Exprs.arrayLiteralCommonTyWithEnvFuel? (fuel : Nat) (env : TypeEnv)
    (exprs : List Expr) : Option Ty :=
  match fuel with
  | 0 => none
  | Nat.succ fuel =>
      match exprs with
      | [] => none
      | first :: rest => do
          let firstTy ← Expr.arrayLiteralElemTyWithEnvFuel? fuel env first
          let info ←
            Exprs.arrayLiteralCommonInfoFromWithEnvFuel?
              fuel env (first, firstTy) rest
          some info.snd

def Exprs.arrayLiteralCommonInfoFromWithEnvFuel? (fuel : Nat) (env : TypeEnv)
    (current : Expr × Ty) : List Expr -> Option (Expr × Ty)
  | [] => some current
  | expr :: rest =>
      match fuel with
      | 0 => none
      | Nat.succ fuel => do
          let ty ← Expr.arrayLiteralElemTyWithEnvFuel? fuel env expr
          let next ← arrayLiteralCommonInfo? current (expr, ty)
          Exprs.arrayLiteralCommonInfoFromWithEnvFuel? fuel env next rest

/-- ITEM-1: lower an inline array literal in an ARGUMENT value position
    (`abi.encode*`/packed/concat/event/error args) whose element type is only
    recoverable WITH the env (storage `bytes`/`string`/array state variables,
    storage-pointer locals). Types the literal env-aware, then lowers it
    through the env-aware `Expr.array` arm at that target, so each element
    materializes (state `bytes` → the contents read; storage locals stay
    refs for the runtime value-use materializer). Callers use this ONLY as a
    decline-fallback — it runs after the env-less path has already returned
    `none`, so every previously-accepted program keeps its byte-identical
    lowering. -/
def Expr.abiArrayLiteralWithEnvFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) (expr : Expr) : Option (Ty × CoreExpr) :=
  match fuel with
  | 0 => none
  | Nat.succ fuel =>
      match expr with
      | Expr.array elems => do
          let elemTy ← Exprs.arrayLiteralCommonTyWithEnvFuel? fuel env elems
          let arrTy := Ty.array elemTy (some elems.length)
          let coreExpr ←
            Expr.toCoreAsWithEnvFuel? fuel storageNames env arrTy expr
          some (arrTy, coreExpr)
      | _ => none

/-- STAGE-D #193: env-aware lowering of ONE `abi.encode`/`abi.encodeWithSelector`
    argument. TC1 `bytesN`-common-type conditionals stay on the dedicated ternary
    widening; a narrow-checked-arithmetic argument
    (`Expr.abiArgNeedsEnvCleanup?`) is lowered at its own inferred source type
    through the full env-aware recursion so the operand-width cleanup fires;
    every other argument keeps the byte-identical env-less
    `Expr.toAbiEncodeArg?`. Env-aware lowering that returns `none` (e.g. a state
    variable whose type is not in `env`) also falls back, preserving acceptance
    and byte-identity. -/
def Expr.toAbiEncodeArgWithEnvFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) (expr : Expr) : Option (CoreTy × CoreExpr) :=
  match fuel with
  | 0 => Expr.toAbiEncodeArg? storageNames expr
  | Nat.succ fuel =>
  match Expr.abiEncodeFixedBytesTernary? storageNames env expr with
  | some (ty, core) => do
      let coreTy ← Ty.toCore? ty
      some (coreTy, core)
  | none =>
      if Expr.abiArgNeedsEnvCleanup? expr then
        match (do
            let ty ← Expr.abiTyWithEnv? env expr
            let coreTy ← Ty.toCore? ty
            let coreExpr ← Expr.toCoreAsWithEnvFuel? fuel storageNames env ty expr
            some (coreTy, coreExpr)) with
        | some result => some result
        | none => Expr.toAbiEncodeArgOrEnvArrayFuel? fuel storageNames env expr
      else
        Expr.toAbiEncodeArgOrEnvArrayFuel? fuel storageNames env expr

/-- ITEM-1: the env-less `abi.encode*` argument lowering, with the env-aware
    array-literal DECLINE-fallback — fires only where `Expr.toAbiEncodeArg?`
    already returned `none` (previously an over-reject), so accepted programs
    are byte-identical. -/
def Expr.toAbiEncodeArgOrEnvArrayFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) (expr : Expr) : Option (CoreTy × CoreExpr) :=
  match Expr.toAbiEncodeArg? storageNames expr with
  | some result => some result
  | none =>
      match fuel with
      | 0 => none
      | Nat.succ fuel => do
          let (ty, coreExpr) ←
            Expr.abiArrayLiteralWithEnvFuel? fuel storageNames env expr
          let coreTy ← Ty.toCore? ty
          some (coreTy, coreExpr)

/-- STAGE-D #193: `abi.encodePacked`/`bytes.concat`/`string.concat` counterpart of
    `Expr.toAbiEncodeArgWithEnvFuel?` — keeps the SOURCE type so
    `Tys.packedTopWidths`/`Tys.allBytesConcatArgs` still see the packed widths. -/
def Expr.toAbiEncodeSourceArgWithEnvFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) (expr : Expr) : Option (Ty × CoreTy × CoreExpr) :=
  match fuel with
  | 0 => Expr.toAbiEncodeSourceArg? storageNames expr
  | Nat.succ fuel =>
  match Expr.abiEncodeFixedBytesTernary? storageNames env expr with
  | some (ty, core) => do
      let coreTy ← Ty.toCore? ty
      some (ty, coreTy, core)
  | none =>
      if Expr.abiArgNeedsEnvCleanup? expr then
        match (do
            let ty ← Expr.abiTyWithEnv? env expr
            let coreTy ← Ty.toCore? ty
            let coreExpr ← Expr.toCoreAsWithEnvFuel? fuel storageNames env ty expr
            some (ty, coreTy, coreExpr)) with
        | some result => some result
        | none =>
            Expr.toAbiEncodeSourceArgOrEnvArrayFuel? fuel storageNames env expr
      else
        Expr.toAbiEncodeSourceArgOrEnvArrayFuel? fuel storageNames env expr

/-- ITEM-1: source-typed twin of `Expr.toAbiEncodeArgOrEnvArrayFuel?`
    (`abi.encodePacked`/`bytes.concat` keep the SOURCE type for packed
    widths); the env-aware array fallback fires only on env-less decline. -/
def Expr.toAbiEncodeSourceArgOrEnvArrayFuel? (fuel : Nat)
    (storageNames : List Name) (env : TypeEnv) (expr : Expr) :
    Option (Ty × CoreTy × CoreExpr) :=
  match Expr.toAbiEncodeSourceArg? storageNames expr with
  | some result => some result
  | none =>
      match fuel with
      | 0 => none
      | Nat.succ fuel => do
          let (ty, coreExpr) ←
            Expr.abiArrayLiteralWithEnvFuel? fuel storageNames env expr
          let coreTy ← Ty.toCore? ty
          some (ty, coreTy, coreExpr)

def Args.toAbiEncodeWithEnvFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) : List Arg -> Option (List CoreTy × List CoreExpr)
  | [] => some ([], [])
  | Arg.positional expr :: rest =>
      match fuel with
      | 0 => Args.toAbiEncode? storageNames (Arg.positional expr :: rest)
      | Nat.succ fuel => do
          let (coreTy, coreExpr) ←
            Expr.toAbiEncodeArgWithEnvFuel? fuel storageNames env expr
          let (tys, coreExprs) ←
            Args.toAbiEncodeWithEnvFuel? fuel storageNames env rest
          some (coreTy :: tys, coreExpr :: coreExprs)
  | Arg.named _ _ :: _ => none

def Args.toAbiEncodeSourceWithEnvFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) : List Arg -> Option (List Ty × List CoreTy × List CoreExpr)
  | [] => some ([], [], [])
  | Arg.positional expr :: rest =>
      match fuel with
      | 0 => Args.toAbiEncodeSource? storageNames (Arg.positional expr :: rest)
      | Nat.succ fuel => do
          let (sourceTy, coreTy, coreExpr) ←
            Expr.toAbiEncodeSourceArgWithEnvFuel? fuel storageNames env expr
          let (sourceTys, coreTys, coreExprs) ←
            Args.toAbiEncodeSourceWithEnvFuel? fuel storageNames env rest
          some (sourceTy :: sourceTys, coreTy :: coreTys, coreExpr :: coreExprs)
  | Arg.named _ _ :: _ => none

def TupleItems.toAbiEncodeSourceWithEnvFuel? (fuel : Nat) (storageNames : List Name)
    (env : TypeEnv) :
    List TupleItem -> Option (List Ty × List CoreTy × List CoreExpr)
  | [] => some ([], [], [])
  | TupleItem.value expr :: rest =>
      match fuel with
      | 0 => TupleItems.toAbiEncodeSource? storageNames (TupleItem.value expr :: rest)
      | Nat.succ fuel => do
          let (sourceTy, coreTy, coreExpr) ←
            Expr.toAbiEncodeSourceArgWithEnvFuel? fuel storageNames env expr
          let (sourceTys, coreTys, coreExprs) ←
            TupleItems.toAbiEncodeSourceWithEnvFuel? fuel storageNames env rest
          some (sourceTy :: sourceTys, coreTy :: coreTys, coreExpr :: coreExprs)
  | TupleItem.hole :: _ => none

end

/-- The unified env-aware typed expression lowering (R2). All callers use this
    (or the binary wrappers below); the fuel-carrying recursion is an
    implementation detail. -/
def Expr.toCoreAsWithEnv? (storageNames : List Name) (env : TypeEnv)
    (targetTy : Ty) (expr : Expr) : Option CoreExpr :=
  Expr.toCoreAsWithEnvFuel? defaultEnvLoweringFuel storageNames env targetTy expr

/-- Lower a state-rooted storage path while preserving checked evaluation of
    narrow index expressions. Storage-pointer declarations and storage-ref
    parameter binding used `storagePathCore?`, whose env-less index lowering
    turned `items[a+b]` (`uint8 a,b`) into a 256-bit addition. -/
def Expr.storagePathCoreWithEnv? (storageNames : List Name) (env : TypeEnv) :
    Expr -> Option (Name × List CoreExpr)
  | Expr.ident name =>
      match stateNameRuntimeKey? name storageNames with
      | some key => some (key, [])
      | none => none
  | Expr.index base index => do
      let (name, indexes) ← Expr.storagePathCoreWithEnv? storageNames env base
      let indexCore ←
        if Expr.abiArgNeedsEnvCleanup? index then do
          let indexTy ← Expr.abiTyWithEnv? env index
          let _ ← Ty.narrowIntCastTarget? indexTy
          Expr.toCoreAsWithEnv? storageNames env indexTy index
        else
          Expr.toCore? storageNames index
      some (name, indexes ++ [indexCore])
  | _ => none

/-- Resolve a path rooted at an existing storage-reference local while lowering
    every index at its Solidity source type. -/
def Expr.storageRefPathCoreWithEnv? (storageRefEnv : StorageRefEnv)
    (storageNames : List Name) (env : TypeEnv) :
    Expr -> Option (Name × List CoreExpr)
  | Expr.ident name =>
      if (stateNameRuntimeKey? name storageNames).isSome then
        none
      else if StorageRefEnv.isStorageRef storageRefEnv name then
        some (name, [])
      else
        none
  | Expr.index base index => do
      let (name, indexes) ←
        Expr.storageRefPathCoreWithEnv? storageRefEnv storageNames env base
      let indexCore ←
        if Expr.abiArgNeedsEnvCleanup? index then do
          let indexTy ← Expr.abiTyWithEnv? env index
          Expr.toCoreAsWithEnv? storageNames env indexTy index
        else
          Expr.toCore? storageNames index
      some (name, indexes ++ [indexCore])
  | _ => none

/-- FB-COMPOUND (S, bare-literal-rhs-of-compound-bitwise-assign-on-bytesn):
    a compound BITWISE assignment (`|=` / `&=` / `^=`) whose LValue is a `bytesN`
    must lower its RHS AT THE LVALUE'S `bytesN` TYPE. The general
    `Expr.toCoreAssignOpWithEnv?` lowers the RHS env-LESS (`Expr.toCore?`), so a
    bare (uncast) hex/string literal stayed a dynamic byte-string value and the
    bitwise op had no enumerated `bytesN`-vs-bytestring case → Panic 0. solc
    converts the RHS to the LValue type (`b |= hex"…"` ≡ `b = b | bytesN(hex"…")`),
    so lowering the RHS through the target-aware `Expr.toCoreAsWithEnv?` at the
    `bytesN` type reproduces it. Restricted to the in-lane bitwise ops (`&= |= ^=`),
    whose RHS shares the LValue type; `<<=`/`>>=` take a shift COUNT (not a bytesN)
    and keep the general path (their width-mask handling is separate). Returns
    `none` for every non-`bytesN` LValue and every non-bitwise op, so the caller
    falls through to the unchanged `Expr.toCoreAssignOpWithEnv?` path. -/
def Expr.toCoreAssignOpBytesNBitwiseRhsAware? (storageNames : List Name)
    (env : TypeEnv) : Expr -> Option CoreExpr
  | Expr.assign lhs op rhs => do
      let coreOp ←
        match op with
        | AssignOp.bitAndAssign => some SolidCore.Solidity.Source.BinaryOp.bitAnd
        | AssignOp.bitOrAssign => some SolidCore.Solidity.Source.BinaryOp.bitOr
        | AssignOp.bitXorAssign => some SolidCore.Solidity.Source.BinaryOp.bitXor
        | _ => none
      let lhsTy ← Expr.abiTyWithEnv? env lhs
      let _ ← Ty.fixedBytesSize? lhsTy
      let lhsCore ← Expr.toCoreLValue? storageNames lhs
      let rhsCore ← Expr.toCoreAsWithEnv? storageNames env lhsTy rhs
      let cleanup ← Ty.toCoreValueCleanup? lhsTy
      some
        (SolidCore.Solidity.Source.Expr.assignOpCleanupExpr
          lhsCore.toExpr coreOp rhsCore cleanup)
  | _ => none

/-- WS1 (H, external-call args): the env-aware argument lowerer threaded into
    the external-call ABI encoding (`Expr.externalCallAbiWithKindEnv?`'s
    `argEnvLower`). A FLAGGED positional argument (narrow checked arithmetic,
    a flagged builtin, or a flagged index read — `Expr.abiArgNeedsEnvCleanup?`)
    is lowered at its declared parameter type through the full env-aware
    recursion, so `this.sink(a + b)` (`uint8 a,b`) Panics 0x11 while building
    the calldata — in the CALLER, before the call (and therefore NOT caught by
    a surrounding `try`: the interpreter propagates calldata-evaluation
    failures past the catch clauses). Every unflagged argument returns `none`,
    keeping the env-less core byte-identically. -/
def Expr.externalCallArgEnvLower (storageNames : List Name) (env : TypeEnv)
    (ty : Ty) (expr : Expr) : Option CoreExpr :=
  if Expr.abiArgNeedsEnvCleanup? expr then
    Expr.toCoreAsWithEnv? storageNames env ty expr
  else
    none

def Expr.binaryToCoreWithEnvTyped? (storageNames : List Name) (env : TypeEnv)
    (op : BinaryOp) (lhs rhs : Expr) : Option (Ty × CoreExpr) :=
  Expr.binaryToCoreWithEnvTypedFuel?
    defaultEnvLoweringFuel storageNames env op lhs rhs

def Expr.binaryToCoreWithEnv? (storageNames : List Name) (env : TypeEnv)
    (op : BinaryOp) (lhs rhs : Expr) : Option CoreExpr :=
  match Expr.binaryToCoreWithEnvTyped? storageNames env op lhs rhs with
  | some (_, coreExpr) => some coreExpr
  | none => none

/-- R2 (Stage C): lower a call-free CONDITION (while/for/do-while/if/require/
    assert) through the env-aware typed lowering at `Ty.bool` FIRST — so
    narrow (`uintN`/`intN`, N < 256) checked arithmetic inside the condition's
    comparison operands keeps its operand-width cleanup (Panic 0x11 on
    overflow in a checked block, width-wrap in `unchecked`), exactly as solc
    evaluates conditions with full type annotations. Falls back to the
    env-less `Expr.toCore?` so no previously-accepted condition regresses;
    `none` only when both fail (e.g. a call-bearing condition, which the
    statement-level call-hoisting desugars handle). -/
def Expr.conditionCoreWithEnv? (storageNames : List Name) (env : TypeEnv)
    (cond : Expr) : Option CoreExpr :=
  match Expr.toCoreAsWithEnv? storageNames env Ty.bool cond with
  | some condCore => some condCore
  | none => Expr.toCore? storageNames cond

/-- ITEM-1: env-less event/error argument lowering with the env-aware
    array-literal DECLINE-fallback (`[storageBytes, …]` as an emit/revert
    argument) — fires only where `Expr.toCore?` already declined. -/
def Expr.abiArgCoreOrEnvArray? (storageNames : List Name) (env : TypeEnv)
    (expr : Expr) : Option CoreExpr :=
  match Expr.toCore? storageNames expr with
  | some coreExpr => some coreExpr
  | none =>
      (Expr.abiArrayLiteralWithEnvFuel?
          defaultEnvLoweringFuel storageNames env expr).map Prod.snd

/-- #201 (D/E): env-aware lowering of ONE event/error argument. A flagged
    argument (narrow checked arithmetic, or an abi/hash/concat builtin whose
    own arguments are flagged — `Expr.abiArgNeedsEnvCleanup?`) is lowered at
    its own inferred type through the full env-aware recursion so its
    operand-width Panic 0x11 fires (`emit EB(abi.encode(a + b))`,
    `emit EMix(a + b, …)`, `revert Err(abi.encode(a + b))`); every other
    argument keeps the byte-identical env-less `Expr.toCore?` (also the
    fallback when the env-aware path declines — ITEM-1 adds the env-aware
    array-literal decline-fallback on both branches). -/
def Expr.abiArgCoreWithEnvCleanup? (storageNames : List Name) (env : TypeEnv)
    (expr : Expr) : Option CoreExpr :=
  if Expr.abiArgNeedsEnvCleanup? expr then
    match (do
        let ty ← Expr.abiTyWithEnv? env expr
        Expr.toCoreAsWithEnv? storageNames env ty expr) with
    | some coreExpr => some coreExpr
    | none => Expr.abiArgCoreOrEnvArray? storageNames env expr
  else
    Expr.abiArgCoreOrEnvArray? storageNames env expr

/-- Lower an indexable base recursively without coercing mapping-valued
    intermediate reads to an ABI type. This is used when the outer index is an
    internal call that is hoisted separately. -/
def Expr.indexBaseCoreWithEnvCleanup? (storageNames : List Name) (env : TypeEnv) :
    Expr -> Option CoreExpr
  | Expr.index base key => do
      let keyCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env key
      match base with
      | Expr.ident name =>
          match stateNameRuntimeKey? name storageNames with
          | some storageKey =>
              some (SolidCore.Solidity.Source.Expr.storageIndex storageKey keyCore)
          | none => do
              let baseCore ← Expr.toCore? storageNames base
              some (SolidCore.Solidity.Source.Expr.index baseCore keyCore)
      | _ => do
          let baseCore ← Expr.indexBaseCoreWithEnvCleanup? storageNames env base
          match Expr.abiTyWithEnv? env base with
          | some ty =>
              match Ty.fixedBytesSize? ty with
              | some size =>
                  some
                    (SolidCore.Solidity.Source.Expr.fixedBytesIndex
                      size baseCore keyCore)
              | none =>
                  some (SolidCore.Solidity.Source.Expr.index baseCore keyCore)
          | none =>
              some (SolidCore.Solidity.Source.Expr.index baseCore keyCore)
  | other => Expr.toCore? storageNames other

/-- Build an outer index read whose base may itself contain narrow checked
    index expressions. -/
def Expr.indexReadCoreBuilderWithEnvCleanup? (storageNames : List Name)
    (env : TypeEnv) (base : Expr) : Option (CoreExpr -> CoreExpr) := do
  if !Expr.abiArgNeedsEnvCleanup? base then
    Expr.indexReadCoreBuilder? storageNames base
  else
    let baseCore ← Expr.indexBaseCoreWithEnvCleanup? storageNames env base
    match Expr.abiTyWithEnv? env base with
    | some ty =>
        match Ty.fixedBytesSize? ty with
        | some size =>
            some (fun idx =>
              SolidCore.Solidity.Source.Expr.fixedBytesIndex size baseCore idx)
        | none =>
            some (fun idx => SolidCore.Solidity.Source.Expr.index baseCore idx)
    | none =>
        some (fun idx => SolidCore.Solidity.Source.Expr.index baseCore idx)

/-- #201 (D/E): does any positional argument need the env-aware cleanup? Gates
    the emit/revert reroutes so every unflagged statement keeps its existing
    lowering byte-identically. -/
def Args.anyAbiArgNeedsEnvCleanup (args : List Arg) : Bool :=
  args.any (fun a =>
    match a with
    | Arg.positional e => Expr.abiArgNeedsEnvCleanup? e
    | Arg.named _ _ => false)

/-- #201 (D/E): positional-argument list counterpart of
    `Expr.abiArgCoreWithEnvCleanup?` (event/custom-error argument lists). -/
def Args.toCoreExprsWithEnvCleanup? (storageNames : List Name)
    (env : TypeEnv) : List Arg -> Option (List CoreExpr)
  | [] => some []
  | Arg.positional e :: rest => do
      let coreExpr ← Expr.abiArgCoreWithEnvCleanup? storageNames env e
      let coreExprs ← Args.toCoreExprsWithEnvCleanup? storageNames env rest
      some (coreExpr :: coreExprs)
  | Arg.named _ _ :: _ => none

/-- Lower a call-free `require(cond, Error(args...))` through the env-aware
    paths when an error argument contains narrow checked arithmetic.  The
    ordinary effect lowering is env-less, so it otherwise turns
    `require(false, E(a + b > 5))` (`uint8 a,b`) into `E(true)` instead of
    evaluating `a + b` at uint8 and Panicking 0x11 first.  Returning `none`
    preserves the existing internal/external-call hoisting chain. -/
def Expr.requireCustomWithEnvCleanup? (storageNames : List Name)
    (env : TypeEnv) : Expr -> Option CoreStmt
  | Expr.call (Expr.ident "require")
      [ Arg.positional cond
      , Arg.positional (Expr.call (Expr.ident errorName) errorArgs) ] =>
      if Args.anyAbiArgNeedsEnvCleanup errorArgs then do
        let condCore ← Expr.conditionCoreWithEnv? storageNames env cond
        let coreArgs ←
          Args.toCoreExprsWithEnvCleanup? storageNames env errorArgs
        some
          (SolidCore.Solidity.Source.Stmt.requireCustom
            condCore errorName coreArgs)
      else
        none
  | _ => none

def TupleItems.toCoreExprsAsWithEnv? (storageNames : List Name)
    (env : TypeEnv) : List Ty -> List TupleItem -> Option (List CoreExpr)
  | [], [] => some []
  | targetTy :: targetTys, TupleItem.value expr :: rest => do
      let head ← Expr.toCoreAsWithEnv? storageNames env targetTy expr
      let tail ← TupleItems.toCoreExprsAsWithEnv?
        storageNames env targetTys rest
      some (head :: tail)
  | _, _ => none

def Expr.externalFunctionValueCallCore? (storageNames : List Name)
    (env : TypeEnv) :
    Expr -> Option
      (CoreLowLevelCallKind × List Ty × CoreExpr × CoreExpr × CoreExpr ×
        Option CoreExpr × Bool)
  | Expr.call fn args => do
      let fnTy ← Expr.abiTyWithEnv? env fn
      match fnTy with
      | Ty.functionWithLocations paramTys _ returnTys _ mutability
          Visibility.external_ => do
          if paramTys.length == args.length then
            -- LIT-COERCION (#144): encode each arg against its DECLARED parameter
            -- type (reusing #140's `toAbiEncodeArgAgainst?`), so a `bytesN`-typed
            -- parameter receiving a hex/string LITERAL gets the left-aligned word
            -- rather than the literal's own dynamic-`bytes` encoding. Falls back to
            -- the target-blind lowering when a non-literal arg has no derivable
            -- `abiTy?` (preserves prior acceptance; those bytes were already right).
            let (coreTys, coreExprs) ←
              match Args.toAbiEncodeAgainst? storageNames paramTys args with
              | some pair => some pair
              | none => do
                  let coreTys ← Ty.listToCore? paramTys
                  let coreExprs ← Args.toCoreExprs? storageNames args
                  some (coreTys, coreExprs)
            let fnCore ← Expr.toCore? storageNames fn
            let calldataCore :=
              SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
                (SolidCore.Solidity.Source.Expr.externalFunctionSelector
                  fnCore)
                coreTys coreExprs
            some
              ( StateMutability.externalFunctionCallKind mutability
              , returnTys
              , SolidCore.Solidity.Source.Expr.externalFunctionAddress fnCore
              , calldataCore
              , CoreExpr.zero
              , none
              , false )
          else
            none
      | _ => none
  | Expr.callWithOptions fn options args => do
      let fnTy ← Expr.abiTyWithEnv? env fn
      match fnTy with
      | Ty.functionWithLocations paramTys _ returnTys _ mutability
          Visibility.external_ => do
          if paramTys.length == args.length then
            -- LIT-COERCION (#144), options form: same target-aware arg encoding
            -- as the plain `Expr.call` arm above.
            let (coreTys, coreExprs) ←
              match Args.toAbiEncodeAgainst? storageNames paramTys args with
              | some pair => some pair
              | none => do
                  let coreTys ← Ty.listToCore? paramTys
                  let coreExprs ← Args.toCoreExprs? storageNames args
                  some (coreTys, coreExprs)
            let kind := StateMutability.externalFunctionCallKind mutability
            let (valueCore, gasCore?, gasFirst) ←
              StateMutability.externalCallOptionsCore?
                storageNames (some mutability) kind options
            let fnCore ← Expr.toCore? storageNames fn
            let calldataCore :=
              SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
                (SolidCore.Solidity.Source.Expr.externalFunctionSelector
                  fnCore)
                coreTys coreExprs
            some
              ( kind
              , returnTys
              , SolidCore.Solidity.Source.Expr.externalFunctionAddress fnCore
              , calldataCore
              , valueCore
              , gasCore?
              , gasFirst )
          else
            none
      | _ => none
  | _ => none

def Expr.externalFunctionValueCallWithReturnsCore?
    (storageNames : List Name) (env : TypeEnv)
    (namePrefix : String) (expr : Expr)
    (successBody : List CoreBindingDecl -> CoreStmt) : Option CoreStmt := do
  let (kind, returnTys, targetCore, calldataCore, valueCore, gasCore?,
    gasFirst) ←
    Expr.externalFunctionValueCallCore? storageNames env expr
  let returnBindings ← Tys.toExternalReturnBindings? namePrefix returnTys
  let returnAbiCleanups ← Tys.toCoreAbiCleanups? returnTys
  let checkTargetCode := returnTys.isEmpty
  some
    (SolidCore.Solidity.Source.Stmt.tryExternalCall
      kind targetCore calldataCore valueCore gasCore? gasFirst
      checkTargetCode returnBindings returnAbiCleanups
      (successBody returnBindings) [])

def Expr.externalFunctionValueCallDiscardCore?
    (storageNames : List Name) (env : TypeEnv) (expr : Expr) :
    Option CoreStmt := do
  let (kind, _, targetCore, calldataCore, valueCore, gasCore?, gasFirst) ←
    Expr.externalFunctionValueCallCore? storageNames env expr
  some
    (SolidCore.Solidity.Source.Stmt.tryExternalCall
      kind targetCore calldataCore valueCore gasCore? gasFirst true []
      [] SolidCore.Solidity.Source.Stmt.skip [])

def Expr.externalFunctionValueCallSingleReturnCore?
    (storageNames : List Name) (env : TypeEnv) (expr : Expr)
    (useResult : CoreExpr -> CoreStmt) : Option CoreStmt := do
  let (_, returnTys, _, _, _, _, _) ←
    Expr.externalFunctionValueCallCore? storageNames env expr
  match returnTys with
  | [_] =>
      Expr.externalFunctionValueCallWithReturnsCore?
        storageNames env "__extfn" expr
        (fun bindings =>
          match bindings with
          | [binding] =>
              useResult (SolidCore.Solidity.Source.Expr.var binding.name)
          | _ => SolidCore.Solidity.Source.Stmt.skip)
  | _ => none

def Expr.externalFunctionValueCallAssignVarsCore?
    (storageNames : List Name) (env : TypeEnv)
    (targetNames : List Name) (expr : Expr) : Option CoreStmt := do
  let (_, returnTys, _, _, _, _, _) ←
    Expr.externalFunctionValueCallCore? storageNames env expr
  if targetNames.length == returnTys.length then
    Expr.externalFunctionValueCallWithReturnsCore?
      storageNames env "__extfn" expr
      (fun bindings =>
        SolidCore.Solidity.Source.Stmt.block
          (CoreBindingDecls.assignToVars targetNames bindings))
  else
    none

def Expr.externalFunctionValueCallAssignBindingsCorePieces?
    (storageNames : List Name) (env : TypeEnv)
    (bindings : List VarBinding) (expr : Expr) : Option (List CoreStmt) := do
  let (_, returnTys, _, _, _, _, _) ←
    Expr.externalFunctionValueCallCore? storageNames env expr
  if bindings.length == returnTys.length then
    some ()
  else
    none
  let decls ← VarBindings.toCoreTupleDecls? bindings
  let returnBindings ← Tys.toExternalReturnBindings? "__extfn" returnTys
  let assigns ←
    VarBindings.assignFromExternalReturnBindings? bindings returnBindings
  let callCore ←
    Expr.externalFunctionValueCallWithReturnsCore?
      storageNames env "__extfn" expr
      (fun _ => SolidCore.Solidity.Source.Stmt.block assigns)
  some (decls ++ [callCore])

def Expr.externalFunctionValueCallReturnCore?
    (storageNames : List Name) (env : TypeEnv)
    (declaredReturnTys : List Ty) (expr : Expr) : Option CoreStmt := do
  let (_, returnTys, _, _, _, _, _) ←
    Expr.externalFunctionValueCallCore? storageNames env expr
  if declaredReturnTys.length == returnTys.length then
    Expr.externalFunctionValueCallWithReturnsCore?
      storageNames env "__extfnret" expr
      (fun bindings =>
        SolidCore.Solidity.Source.Stmt.returnValues
          (CoreBindingDecls.toVarExprs bindings))
  else
    none

-- EC1: `abi.encodeCall(fnPtr, args)` derives the 4-byte selector AND the
-- argument ENCODE types from the callee's DECLARED parameter types — never from
-- the argument expression types (solc `ExpressionCompiler`/`ABIFunctions`). The
-- env-free `Expr.toCore?` lowering only sees the argument expressions, so the
-- annotate pass (which has the `TypeEnv`) resolves the declared parameter types
-- here and forces each argument to encode at its parameter type. The declared
-- parameter types live in the external-call-kind entries carried in the type
-- env under keys `__external_call_kind:<contract>:<fn>(...)` whose value is a
-- `Ty.function paramTys ...` (see `ExternalCallKindEntry.toTypeEnvEntry?`).
def Expr.encodeCallDeclaredParamTys? (env : TypeEnv)
    (functionPointer : Expr) : Option (List Ty) :=
  match functionPointer with
  | Expr.member target name => do
      let contractName ← Expr.externalCallTargetContractNameWithEnv? env target
      let keyPrefix :=
        externalCallKindTypeEnvPrefix ++ contractName ++ ":" ++ name ++ "("
      env.findSome? (fun entry =>
        if entry.fst.startsWith keyPrefix then
          match entry.snd with
          | Ty.functionWithLocations paramTys _ _ _ _ _ => some paramTys
          | _ => none
        else
          none)
  | _ => none

def Expr.annotateAbiFuel : Nat -> TypeEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let annotate := Expr.annotateAbiFuel fuel env
      let annotateArg : Arg -> Arg
        | Arg.positional argExpr => Arg.positional (annotate argExpr)
        | Arg.named name argExpr => Arg.named name (annotate argExpr)
      let annotateAbiArg : Arg -> Arg
        | Arg.positional argExpr =>
            let annotated := annotate argExpr
            let encoded :=
              match Expr.abiTy? [] annotated with
              | some _ => annotated
              | none =>
                  match Expr.abiTyWithEnv? env annotated with
                  | some ty =>
                      Expr.call (Expr.typeName ty) [Arg.positional annotated]
                  | none => annotated
            Arg.positional encoded
        | Arg.named name argExpr =>
            let annotated := annotate argExpr
            let encoded :=
              match Expr.abiTy? [] annotated with
              | some _ => annotated
              | none =>
                  match Expr.abiTyWithEnv? env annotated with
                  | some ty =>
                      Expr.call (Expr.typeName ty) [Arg.positional annotated]
                  | none => annotated
            Arg.named name encoded
      let annotateOption : CallOption -> CallOption
        | CallOption.named name optionExpr =>
            CallOption.named name (annotate optionExpr)
      let annotateTupleItem : TupleItem -> TupleItem
        | TupleItem.hole => TupleItem.hole
        | TupleItem.value itemExpr => TupleItem.value (annotate itemExpr)
      let annotateAbiTupleItem : TupleItem -> TupleItem
        | TupleItem.hole => TupleItem.hole
        | TupleItem.value itemExpr =>
            let annotated := annotate itemExpr
            let encoded :=
              match Expr.abiTy? [] annotated with
              | some _ => annotated
              | none =>
                  match Expr.abiTyWithEnv? env annotated with
                  | some ty =>
                      Expr.call (Expr.typeName ty) [Arg.positional annotated]
                  | none => annotated
            TupleItem.value encoded
      -- EC1: encode an `abi.encodeCall` argument at its DECLARED parameter type.
      -- When the argument's own ABI type already matches the parameter type (by
      -- ABI canonical form) this is exactly the ordinary abi annotation; when it
      -- differs (implicit conversion — narrow variable, or integer literal vs a
      -- non-`uint256` parameter) the argument is wrapped in an explicit
      -- conversion to the parameter type so both the selector signature and the
      -- encode type are taken from the parameter type, matching solc.
      let annotateEncodeCallArg (paramTy : Ty) (itemExpr : Expr) : Expr :=
        let annotated := annotate itemExpr
        let baseTy? :=
          match Expr.abiTy? [] annotated with
          | some t => some t
          | none => Expr.abiTyWithEnv? env annotated
        match baseTy? with
        | some baseTy =>
            if Ty.abiCanonical? baseTy == Ty.abiCanonical? paramTy then
              match Expr.abiTy? [] annotated with
              | some _ => annotated
              | none =>
                  Expr.call (Expr.typeName baseTy) [Arg.positional annotated]
            else
              Expr.call (Expr.typeName paramTy) [Arg.positional annotated]
        | none => annotated
      let annotateEncodeCallTupleItems
          (paramTys : List Ty) (items : List TupleItem) : List TupleItem :=
        (paramTys.zip items).map (fun (paramTy, item) =>
          match item with
          | TupleItem.hole => TupleItem.hole
          | TupleItem.value itemExpr =>
              TupleItem.value (annotateEncodeCallArg paramTy itemExpr))
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (annotate base) member
      | Expr.index base index => Expr.index (annotate base) (annotate index)
      | Expr.slice base start stop =>
          Expr.slice (annotate base) (start.map annotate) (stop.map annotate)
      | Expr.call (Expr.member (Expr.ident "abi") "encode") args =>
          Expr.call (Expr.member (Expr.ident "abi") "encode")
            (args.map annotateAbiArg)
      | Expr.call (Expr.member (Expr.ident "abi") "encodePacked") args =>
          Expr.call (Expr.member (Expr.ident "abi") "encodePacked")
            (args.map annotateAbiArg)
      | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector") args =>
          Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector")
            (args.map annotateAbiArg)
      | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSignature") args =>
          match args with
          | [] =>
              Expr.call
                (Expr.member (Expr.ident "abi") "encodeWithSignature") []
          | head :: rest =>
              Expr.call
                (Expr.member (Expr.ident "abi") "encodeWithSignature")
                (annotateArg head :: rest.map annotateAbiArg)
      | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
          [Arg.positional functionPointer, Arg.positional (Expr.tuple items)] =>
          match Expr.encodeCallDeclaredParamTys? env functionPointer with
          | some [paramTy@(Ty.struct _ fieldTys)] =>
              -- A resolved one-argument struct constructor is itself an
              -- `Expr.tuple` of fields.  Treating every tuple here as the
              -- encodeCall ARGUMENT LIST flattened that struct: the ABI type
              -- remained `(uint256)` while the value became the scalar `7`,
              -- so encoding failed with Panic(0).  Keep the field tuple as one
              -- explicitly typed argument.  The wrapper also prevents the
              -- later encodeCall lowering from mistaking it for a multi-arg
              -- tuple, while field annotation preserves the usual narrow
              -- arithmetic checks.
              let isStructValue :=
                match Expr.abiTyWithEnv? env (Expr.tuple items) with
                | some tupleTy =>
                    match Ty.abiCanonical? tupleTy,
                        Ty.abiCanonical? paramTy with
                    | some tupleCanonical, some paramCanonical =>
                        tupleCanonical == paramCanonical
                    | _, _ => false
                | none => false
              if fieldTys.length == items.length && isStructValue then
                let annotatedFields :=
                  annotateEncodeCallTupleItems fieldTys items
                Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
                  [ Arg.positional (annotate functionPointer)
                  , Arg.positional
                      (Expr.call (Expr.typeName paramTy)
                        [Arg.positional (Expr.tuple annotatedFields)]) ]
              else
                Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
                  [ Arg.positional (annotate functionPointer)
                  , Arg.positional
                      (Expr.tuple (items.map annotateAbiTupleItem)) ]
          | some paramTys =>
              let annotatedItems :=
                if paramTys.length == items.length then
                  annotateEncodeCallTupleItems paramTys items
                else
                  items.map annotateAbiTupleItem
              Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
                [ Arg.positional (annotate functionPointer)
                , Arg.positional (Expr.tuple annotatedItems) ]
          | none =>
              Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
                [ Arg.positional (annotate functionPointer)
                , Arg.positional
                    (Expr.tuple (items.map annotateAbiTupleItem)) ]
      | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
          [Arg.positional functionPointer, Arg.positional argumentExpr] =>
          let annotatedArg :=
            match Expr.encodeCallDeclaredParamTys? env functionPointer with
            | some [paramTy] =>
                Arg.positional (annotateEncodeCallArg paramTy argumentExpr)
            | _ => annotateAbiArg (Arg.positional argumentExpr)
          Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
            [ Arg.positional (annotate functionPointer)
            , annotatedArg ]
      | Expr.call (Expr.member (Expr.ident "abi") "decode")
          [Arg.positional data, typesExpr] =>
          Expr.call (Expr.member (Expr.ident "abi") "decode")
            [Arg.positional (annotate data), typesExpr]
      | Expr.callWithOptions (Expr.newExpr ty []) options args =>
          Expr.callWithOptions (Expr.newExpr ty [])
            (options.map annotateOption) (args.map annotateAbiArg)
      | Expr.call (Expr.member target name) args =>
          Expr.call (Expr.member (annotate target) name)
            (args.map annotateAbiArg)
      | Expr.callWithOptions (Expr.member target name) options args =>
          Expr.callWithOptions (Expr.member (annotate target) name)
            (options.map annotateOption) (args.map annotateAbiArg)
      | Expr.call (Expr.typeName ty) [Arg.positional argExpr] =>
          let annotated := annotate argExpr
          let encoded :=
            match Expr.abiTy? [] annotated with
            | some _ => annotated
            | none =>
                match Expr.abiTyWithEnv? env annotated with
                | some sourceTy =>
                    Expr.call (Expr.typeName sourceTy)
                      [Arg.positional annotated]
                | none => annotated
          Expr.call (Expr.typeName ty) [Arg.positional encoded]
      | Expr.call fn args =>
          Expr.call (annotate fn) (args.map annotateArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (annotate fn)
            (options.map annotateOption) (args.map annotateArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map annotateAbiArg)
      | Expr.tuple items => Expr.tuple (items.map annotateTupleItem)
      | Expr.array exprs => Expr.array (exprs.map annotate)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (annotate inner)
      | Expr.unary op inner => Expr.unary op (annotate inner)
      | Expr.binary op lhs rhs =>
          let lhs := annotate lhs
          let rhs := annotate rhs
          -- Modifier bodies are lowered after their placeholder is spliced and
          -- therefore use the env-free core expression path.  Preserve the
          -- implicit type of a literal expression compared with a typed local
          -- there (for
          -- example `bytes7 a; while (a == "1234567") _;`) by making the
          -- coercion explicit while the modifier's TypeEnv is still present.
          -- This also records the adoption of a compound numeric constant such
          -- as `int_max == 2**255 - 1`.  Do not wrap a literal-only pair: those
          -- remain solc rational constants and must keep the compile-time folder.
          let lhsAdopts :=
            Expr.isDirectLiteral lhs || Expr.isRawNumberLiteralExpression lhs
          let rhsAdopts :=
            Expr.isDirectLiteral rhs || Expr.isRawNumberLiteralExpression rhs
          if rhsAdopts && !lhsAdopts then
            match Expr.abiTyWithEnv? env lhs with
            | some lhsTy =>
                if implicitLiteralFits lhsTy rhs then
                  Expr.binary op lhs
                    (Expr.call (Expr.typeName lhsTy) [Arg.positional rhs])
                else
                  Expr.binary op lhs rhs
            | none => Expr.binary op lhs rhs
          else if lhsAdopts && !rhsAdopts then
            match Expr.abiTyWithEnv? env rhs with
            | some rhsTy =>
                if implicitLiteralFits rhsTy lhs then
                  Expr.binary op
                    (Expr.call (Expr.typeName rhsTy) [Arg.positional lhs]) rhs
                else
                  Expr.binary op lhs rhs
            | none => Expr.binary op lhs rhs
          else
            Expr.binary op lhs rhs
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (annotate cond) (annotate thenExpr)
            (annotate elseExpr)
      | Expr.assign lhs op rhs => Expr.assign lhs op (annotate rhs)
      | Expr.payableConversion inner => Expr.payableConversion (annotate inner)

def defaultAnnotateAbiFuel : Nat := 1024

def Expr.annotateAbi (env : TypeEnv) (expr : Expr) : Expr :=
  Expr.annotateAbiFuel defaultAnnotateAbiFuel env expr

def Stmt.annotateAbiInSeqFuel :
    Nat -> TypeEnv -> Stmt -> Stmt × TypeEnv
  | 0, env, stmt => (stmt, env)
  | fuel + 1, env, stmt =>
      let annotateExpr := Expr.annotateAbiFuel fuel env
      let annotateStmt (child : Stmt) :=
        (Stmt.annotateAbiInSeqFuel fuel env child).fst
      let annotateSeq (env : TypeEnv) (body : List Stmt) :
          List Stmt × TypeEnv :=
        let step (acc : List Stmt × TypeEnv) (head : Stmt) :
            List Stmt × TypeEnv :=
          let (done, env) := acc
          let (head', env') := Stmt.annotateAbiInSeqFuel fuel env head
          (head' :: done, env')
        let (revBody, finalEnv) :=
          body.foldl step (([] : List Stmt), env)
        (revBody.reverse, finalEnv)
      let annotateClause : CatchClause -> CatchClause
        | CatchClause.clause name params body =>
            let clauseEnv := Parameters.extendTypeEnv "_catch" env params
            CatchClause.clause name params
              ((Stmt.annotateAbiInSeqFuel fuel clauseEnv body).fst)
      -- QUAL-CALLEE (#74/#77): emit/revert/require whose event/error callee is a
      -- MEMBER access (`Base.E`, `C.Err`) must annotate its arguments PLAINLY,
      -- exactly like the bare-ident callee (which hits the `Expr.call fn args`
      -- fallback below). The general `Expr.call (Expr.member target name) args`
      -- arm ABI-WRAPS arguments (for `abi.encode`/external-call callees); event
      -- and custom-error arguments must NOT be wrapped — `EventDecl.encodeFields?`
      -- / the custom-error ABI encoder do that from the field types. Without
      -- this, a qualified emit/revert double-encodes and reverts with
      -- `typeMismatch` (panic 0) or carries wrapped argument values.
      let annotatePlainArgs (args : List Arg) : List Arg :=
        args.map (fun a =>
          match a with
          | Arg.positional e => Arg.positional (annotateExpr e)
          | Arg.named n e => Arg.named n (annotateExpr e))
      let annotateEventErrorCall (callExpr : Expr) : Expr :=
        match callExpr with
        | Expr.call (Expr.member target name) args =>
            Expr.call (Expr.member (annotateExpr target) name)
              (annotatePlainArgs args)
        | other => annotateExpr other
      match stmt with
      | Stmt.empty => (Stmt.empty, env)
      | Stmt.block body =>
          let (body', _) := annotateSeq env body
          (Stmt.block body', env)
      | Stmt.varDecl bindings init =>
          let init' := init.map annotateExpr
          let env' := VarBindings.extendTypeEnv env bindings
          (Stmt.varDecl bindings init', env')
      -- QUAL-CALLEE (#77), require form: `require(cond, Base.Err(a))` — annotate
      -- the member-access custom-error callee's args plainly (see
      -- `annotateEventErrorCall`), not via the ABI-wrapping member-call arm.
      -- Restricted to a user-type qualifier (`Ty.user`) so a builtin member
      -- reason like `require(cond, string.concat(a, b))` keeps its ordinary path.
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [Arg.positional cond,
             Arg.positional
               (Expr.call
                 (Expr.member (Expr.typeName (Ty.user path)) name) errorArgs)]) =>
          (Stmt.expr
            (Expr.call (Expr.ident "require")
              [ Arg.positional (annotateExpr cond)
              , Arg.positional
                  (Expr.call (Expr.member (Expr.typeName (Ty.user path)) name)
                    (annotatePlainArgs errorArgs)) ]), env)
      | Stmt.expr expr => (Stmt.expr (annotateExpr expr), env)
      | Stmt.ifElse cond thenBranch elseBranch =>
          let thenBranch' := annotateStmt thenBranch
          let elseBranch' := elseBranch.map annotateStmt
          (Stmt.ifElse (annotateExpr cond) thenBranch' elseBranch', env)
      | Stmt.whileLoop cond body =>
          (Stmt.whileLoop (annotateExpr cond) (annotateStmt body), env)
      | Stmt.doWhile body cond =>
          (Stmt.doWhile (annotateStmt body) (annotateExpr cond), env)
      | Stmt.forLoop init cond post body =>
          let (init', loopEnv) :=
            match init with
            | some initStmt =>
                let (stmt', env') :=
                  Stmt.annotateAbiInSeqFuel fuel env initStmt
                (some stmt', env')
            | none => (none, env)
          let annotateLoopExpr := Expr.annotateAbiFuel fuel loopEnv
          let body' := (Stmt.annotateAbiInSeqFuel fuel loopEnv body).fst
          (Stmt.forLoop init' (cond.map annotateLoopExpr)
            (post.map annotateLoopExpr) body', env)
      | Stmt.tryCatch expr clauses =>
          (Stmt.tryCatch (annotateExpr expr) (clauses.map annotateClause), env)
      | Stmt.tryCatchReturns expr returns success clauses =>
          let successEnv := Parameters.extendTypeEnv "_try" env returns
          let success' := (Stmt.annotateAbiInSeqFuel fuel successEnv success).fst
          (Stmt.tryCatchReturns (annotateExpr expr) returns success'
            (clauses.map annotateClause), env)
      | Stmt.emitEvent expr => (Stmt.emitEvent (annotateEventErrorCall expr), env)
      | Stmt.revertCall expr =>
          (Stmt.revertCall (annotateEventErrorCall expr), env)
      | Stmt.returnValues expr? =>
          (Stmt.returnValues (expr?.map annotateExpr), env)
      | Stmt.break => (Stmt.break, env)
      | Stmt.continue => (Stmt.continue, env)
      | Stmt.unchecked body => (Stmt.unchecked (annotateStmt body), env)
      | Stmt.inlineAssembly code => (Stmt.inlineAssembly code, env)
      | Stmt.modifierPlaceholder => (Stmt.modifierPlaceholder, env)

def Stmt.annotateAbiFuel (fuel : Nat) (env : TypeEnv) (stmt : Stmt) :
    Stmt :=
  (Stmt.annotateAbiInSeqFuel fuel env stmt).fst

def Stmt.annotateAbi (env : TypeEnv) (stmt : Stmt) : Stmt :=
  Stmt.annotateAbiFuel defaultAnnotateAbiFuel env stmt

def Parameter.toCoreBinding? (fallbackPrefix : String) (index : Nat)
    (param : Parameter) : Option CoreBindingDecl := do
  -- Stage E: a `T storage` binding is a storage POINTER at run time — it binds
  -- reference-preservingly (`bindArgRef?`) and defaults to a storage alias
  -- (`defaultBinding` via `isStorageRef`), so its declared core Ty is never
  -- consulted for coercion. Types with no core form (mapping-containing
  -- structs, bare mappings — common `using`-for library params) therefore get
  -- a placeholder, instead of sinking the whole contract's table build.
  let ty ←
    match Ty.toCore? param.ty with
    | some ty => some ty
    | none =>
        if param.location == some DataLocation.storage then
          some SolidCore.Solidity.Source.Ty.uint256
        else
          none
  let name := param.name.getD (fallbackPrefix ++ toString index)
  -- Reference-signature extension, stage A: mark `T storage` bindings so the
  -- framed internal-call entry binds them as storage POINTERS (see
  -- `BindingDecl.isStorageRef` in `Interpreter.lean`). Only return bindings are
  -- default-bound (parameters bind to argument values), but the flag is set
  -- uniformly from the declared data location.
  some
    { name := name
      ty := ty
      isStorageRef := param.location == some DataLocation.storage }

def Parameters.toCoreBindings? (fallbackPrefix : String)
    (params : List Parameter) : Option (List CoreBindingDecl) :=
  mapOptionIdx (Parameter.toCoreBinding? fallbackPrefix) 0 params

def Parameter.toVarDeclWithArg (fallbackPrefix : String) (index : Nat)
    (param : Parameter) (arg : Expr) : Stmt :=
  Stmt.varDecl
    [{ name := some (param.name.getD (fallbackPrefix ++ toString index))
       ty := some param.ty
       location := param.location }]
    (some arg)

def Parameters.toVarDeclsWithArgs? (fallbackPrefix : String)
    (params : List Parameter) (args : List Expr) : Option (List Stmt) :=
  if params.length == args.length then
    some
      (mapIdx
        (fun index pair =>
          Parameter.toVarDeclWithArg
            fallbackPrefix index pair.fst pair.snd)
        0 (params.zip args))
  else
    none

def Ty.storageReferenceSupported? (ty : Ty) : Option Unit :=
  match Ty.toCore? ty with
  | some _ => some ()
  | none =>
      match Ty.toCoreStorageLayout? ty with
      | some _ => some ()
      | none => none

/-- G#116 (TERNARY-STORAGE-STATELVALUE): resolve ONE branch of a ternary
    storage reference (`b ? s0 : s1`) to the storage-alias DECL statement that
    binds `name` to that branch's storage reference. Mirrors the storage-arg
    branch dispatch below (state-var → `storageAlias`/`storageAliasPath`;
    storage-ref local → `storageAliasFrom`/`storageAliasFromPath`). -/
def Expr.storageRefBranchAliasDeclCore? (storageRefEnv : StorageRefEnv)
    (storageNames : List Name) (name : Name) :
    Expr -> Option CoreStmt
  | Expr.ident target =>
      match stateNameRuntimeKey? target storageNames with
      | some key => some (SolidCore.Solidity.Source.Stmt.storageAlias name key)
      | none =>
          if StorageRefEnv.isStorageRef storageRefEnv target then
            some (SolidCore.Solidity.Source.Stmt.storageAliasFrom name target)
          else
            none
  | arg =>
      match Expr.storageRefPathCore? storageRefEnv storageNames arg with
      | some (source, indexes) =>
          match indexes with
          | [] =>
              some (SolidCore.Solidity.Source.Stmt.storageAliasFrom name source)
          | _ =>
              some
                (SolidCore.Solidity.Source.Stmt.storageAliasFromPath
                  name source indexes)
      | none => do
          let (target, indexes) ← Expr.storagePathCore? storageNames arg
          match indexes with
          | [] =>
              some (SolidCore.Solidity.Source.Stmt.storageAlias name target)
          | _ =>
              some
                (SolidCore.Solidity.Source.Stmt.storageAliasPath
                  name target indexes)

def Parameter.toStorageAwareCoreArgDecl? (storageRefEnv : StorageRefEnv)
    (storageNames : List Name) (env : TypeEnv) (fallbackPrefix : String)
    (index : Nat) (param : Parameter) (arg : Expr) : Option CoreStmt := do
  let name := param.name.getD (fallbackPrefix ++ toString index)
  match param.location with
  | some DataLocation.storage =>
      let _ ← Ty.storageReferenceSupported? param.ty
      match arg with
      | Expr.ternary cond thenExpr elseExpr => do
          -- G#116: a ternary of two storage references passed to a `storage`-ref
          -- parameter aliases the SELECTED branch (like the varDecl form). Emit
          -- an `ifElse` binding the temp/param to the chosen branch's alias.
          let condCore ← Expr.toCore? storageNames cond
          let thenStmt ←
            Expr.storageRefBranchAliasDeclCore? storageRefEnv storageNames
              name thenExpr
          let elseStmt ←
            Expr.storageRefBranchAliasDeclCore? storageRefEnv storageNames
              name elseExpr
          some
            (SolidCore.Solidity.Source.Stmt.ifElse condCore thenStmt elseStmt)
      | Expr.ident target =>
          match stateNameRuntimeKey? target storageNames with
          | some key =>
            some (SolidCore.Solidity.Source.Stmt.storageAlias name key)
          | none =>
          if StorageRefEnv.isStorageRef storageRefEnv target then
            some (SolidCore.Solidity.Source.Stmt.storageAliasFrom name target)
          else
            none
      | _ => do
          match
              Expr.storageRefPathCore? storageRefEnv storageNames arg
          with
          | some (source, indexes) =>
              match indexes with
              | [] =>
                  some
                    (SolidCore.Solidity.Source.Stmt.storageAliasFrom
                      name source)
              | _ =>
                  some
                    (SolidCore.Solidity.Source.Stmt.storageAliasFromPath
                      name source indexes)
          | none => do
              let (target, indexes) ←
                Expr.storagePathCoreWithEnv? storageNames env arg
              match indexes with
              | [] =>
                  some (SolidCore.Solidity.Source.Stmt.storageAlias name target)
              | _ =>
                  some
                    (SolidCore.Solidity.Source.Stmt.storageAliasPath
                      name target indexes)
  | _ => do
      let coreTy ← Ty.toCore? param.ty
      let initCore ←
        match Expr.toCoreAsWithEnv? storageNames env param.ty arg with
        | some coreExpr => some coreExpr
        | none => Expr.toCore? storageNames arg
      if param.location == some DataLocation.memory then
        some
          (SolidCore.Solidity.Source.Stmt.memoryVarDecl
            coreTy name (some initCore))
      else
        some
          (SolidCore.Solidity.Source.Stmt.varDecl
            coreTy name (some initCore))

def Parameters.toStorageAwareCoreArgDecls? (storageRefEnv : StorageRefEnv)
    (storageNames : List Name) (env : TypeEnv) (fallbackPrefix : String)
    (params : List Parameter) (args : List Expr) :
    Option (List CoreStmt) :=
  if params.length == args.length then
    mapOptionIdx
      (fun index pair =>
        Parameter.toStorageAwareCoreArgDecl?
          storageRefEnv storageNames env fallbackPrefix index pair.fst pair.snd)
      0 (params.zip args)
  else
    none

def Parameter.toCoreCleanupStmt? (fallbackPrefix : String)
    (index : Nat) (param : Parameter) : Option CoreStmt :=
  match param.location with
  | some DataLocation.storage => some SolidCore.Solidity.Source.Stmt.skip
  | some DataLocation.memory => do
      let coreTy ← Ty.toCore? param.ty
      let name := param.name.getD (fallbackPrefix ++ toString index)
      some (SolidCore.Solidity.Source.Stmt.memoryLocalize coreTy name)
  | _ =>
      match param.ty with
      | Ty.uint bits => do
          let bits := if bits == 0 then 256 else bits
          if 0 < bits && bits <= 256 then
            let name := param.name.getD (fallbackPrefix ++ toString index)
            some
              (SolidCore.Solidity.Source.Stmt.assign
                (SolidCore.Solidity.Source.LValue.var name)
                (SolidCore.Solidity.Source.Expr.uintCleanup bits
                  (SolidCore.Solidity.Source.Expr.var name)))
          else
            none
      | Ty.int bits => do
          let bits := if bits == 0 then 256 else bits
          if 0 < bits && bits <= 256 then
            let name := param.name.getD (fallbackPrefix ++ toString index)
            some
              (SolidCore.Solidity.Source.Stmt.assign
                (SolidCore.Solidity.Source.LValue.var name)
                (SolidCore.Solidity.Source.Expr.intCleanup bits
                  (SolidCore.Solidity.Source.Expr.var name)))
          else
            none
      | _ => some SolidCore.Solidity.Source.Stmt.skip

def Parameters.toCoreCleanupStmts? (fallbackPrefix : String)
    (params : List Parameter) : Option (List CoreStmt) :=
  mapOptionIdx (Parameter.toCoreCleanupStmt? fallbackPrefix) 0 params

def Parameter.toCoreMemoryLocalizeStmt? (fallbackPrefix : String)
    (localizeCalldata : Bool)
    (index : Nat) (param : Parameter) : Option CoreStmt :=
  if param.location == some DataLocation.memory then do
    let coreTy ← Ty.toCore? param.ty
    let name := param.name.getD (fallbackPrefix ++ toString index)
    some (SolidCore.Solidity.Source.Stmt.memoryLocalize coreTy name)
  else if localizeCalldata && param.location == some DataLocation.calldata then do
    -- CALLDATA-located AGGREGATE return (`returns (uint256[] calldata)`):
    -- normalize to memory exactly like a memory-located return. solc's
    -- `FunctionType::asExternallyCallableFunction` performs the same
    -- calldata->memory normalization at the external boundary, and the model
    -- must materialize the returned value before the return re-encode: a
    -- lazily-decoded calldata aggregate carries `Value.abiLazy` element
    -- wrappers, and the un-localized return path raw-coerces them into a
    -- typeMismatch (raw Panic 0x00) where the EVM returns the array. Scoped
    -- to memory-aggregate core types: `bytes`/`string` calldata returns
    -- (core `bytesCalldata`) already return correctly and keep their
    -- byte-identical prologue. Gated to EXTERNAL/PUBLIC entry functions
    -- (`localizeCalldata`) — an INTERNAL calldata-returning callee keeps its
    -- pointer-return discipline (pointer-return-definite lane).
    let coreTy ← Ty.toCore? param.ty
    if CoreTy.isMemoryAggregate coreTy then
      let name := param.name.getD (fallbackPrefix ++ toString index)
      some (SolidCore.Solidity.Source.Stmt.memoryLocalize coreTy name)
    else
      some SolidCore.Solidity.Source.Stmt.skip
  else
    some SolidCore.Solidity.Source.Stmt.skip

def Parameters.toCoreMemoryLocalizeStmts? (fallbackPrefix : String)
    (params : List Parameter) (localizeCalldata : Bool := false) :
    Option (List CoreStmt) :=
  mapOptionIdx
    (Parameter.toCoreMemoryLocalizeStmt? fallbackPrefix localizeCalldata)
    0 params

/-- Reserved storage-alias target for a not-yet-assigned `T storage` named
    return. Single source of truth lives in the interpreter (the framed
    internal-call entry binds storage-ref returns to it via
    `BindingDecl.defaultBinding`); elaboration's caller-side return temps
    (`toStorageAwareDefaultCoreDecl?`) use the same target. -/
def uninitializedStorageReturnTarget : Name :=
  SolidCore.Solidity.Source.uninitializedStorageReturnTarget

def Parameter.toDefaultVarDecl (fallbackPrefix : String) (index : Nat)
    (param : Parameter) : Stmt :=
  Stmt.varDecl
    [{ name := some (param.name.getD (fallbackPrefix ++ toString index))
       ty := some param.ty
       location := param.location }]
    none

def Parameters.toDefaultVarDecls (fallbackPrefix : String)
    (params : List Parameter) : List Stmt :=
  mapIdx (Parameter.toDefaultVarDecl fallbackPrefix) 0 params

def Parameter.toStorageAwareDefaultCoreDecl? (fallbackPrefix : String)
    (index : Nat) (param : Parameter) : Option CoreStmt := do
  let name := param.name.getD (fallbackPrefix ++ toString index)
  match param.location with
  | some DataLocation.storage =>
      let _ ← Ty.storageReferenceSupported? param.ty
      some
        (SolidCore.Solidity.Source.Stmt.storageAlias
          name uninitializedStorageReturnTarget)
  | _ => do
      let coreTy ← Ty.toCore? param.ty
      if param.location == some DataLocation.memory then
        some (SolidCore.Solidity.Source.Stmt.memoryVarDecl coreTy name none)
      else
        some (SolidCore.Solidity.Source.Stmt.varDecl coreTy name none)

def Parameters.toStorageAwareDefaultCoreDecls?
    (fallbackPrefix : String) (params : List Parameter) :
    Option (List CoreStmt) :=
  mapOptionIdx
    (Parameter.toStorageAwareDefaultCoreDecl? fallbackPrefix) 0 params

def VarBinding.toCoreDecl? (binding : VarBinding) : Option CoreStmt := do
  let name ← binding.name
  let ty ← binding.ty
  let coreTy ← Ty.toCore? ty
  if binding.location == some DataLocation.memory then
    some (SolidCore.Solidity.Source.Stmt.memoryVarDecl coreTy name none)
  else
    some (SolidCore.Solidity.Source.Stmt.varDecl coreTy name none)

def VarBindings.toCoreDecls? :
    List VarBinding -> Option (List CoreStmt) :=
  mapOption VarBinding.toCoreDecl?

def VarBindings.toCoreDeclsExceptStorageReturns? :
    List VarBinding -> List Bool -> Option (List CoreStmt)
  | [], [] => some []
  | binding :: bindings, isStorageReturn :: flags => do
      let tail ←
        VarBindings.toCoreDeclsExceptStorageReturns? bindings flags
      match binding.name with
      | none => some tail
      | some name =>
          if isStorageReturn then
            match binding.location with
            | some DataLocation.storage => some tail
            | _ => none
          else
            match binding.ty with
            | some ty => do
                let coreTy ← Ty.toCore? ty
                let head :=
                  if binding.location == some DataLocation.memory then
                    SolidCore.Solidity.Source.Stmt.memoryVarDecl
                      coreTy name none
                  else
                    SolidCore.Solidity.Source.Stmt.varDecl
                      coreTy name none
                some (head :: tail)
            | none => none
  | _, _ => none

def VarBindings.assignFromReturnBindingsWithStorageRefs? :
    List VarBinding -> List CoreBindingDecl -> List Bool ->
      Option (List CoreStmt)
  | [], [], [] => some []
  | binding :: bindings, ret :: returns, isStorageReturn :: flags => do
      let tail ←
        VarBindings.assignFromReturnBindingsWithStorageRefs?
          bindings returns flags
      match binding.name with
      | none => some tail
      | some name =>
          if isStorageReturn then
            match binding.location with
            | some DataLocation.storage =>
                some
                  (SolidCore.Solidity.Source.Stmt.storageAliasFrom
                    name ret.name :: tail)
            | _ => none
          else
            some
              (SolidCore.Solidity.Source.Stmt.assign
                (SolidCore.Solidity.Source.LValue.var name)
                (SolidCore.Solidity.Source.Expr.var ret.name) :: tail)
  | _, _, _ => none

def VarBindings.names? : List VarBinding -> Option (List Name)
  | [] => some []
  | binding :: rest => do
      let name ← binding.name
      let tail ← VarBindings.names? rest
      some (name :: tail)

def VarBindings.sourceTys? : List VarBinding -> Option (List Ty)
  | [] => some []
  | binding :: rest => do
      let ty ← binding.ty
      let tail ← VarBindings.sourceTys? rest
      some (ty :: tail)

def Parameters.abiCanonicalTypes? (params : List Parameter) :
    Option (List String) :=
  mapOption (fun param => Ty.abiCanonical? param.ty) params

def FunctionDecl.abiSignature? (decl : FunctionDecl) : Option String := do
  match decl.kind with
  | FunctionKind.function => some ()
  | _ => none
  let name ← decl.name
  let paramTypes ← Parameters.abiCanonicalTypes? decl.params
  some (name ++ "(" ++ joinStringsWith "," paramTypes ++ ")")

def FunctionDecl.abiSelector? (decl : FunctionDecl) : Option Word := do
  let signature ← FunctionDecl.abiSignature? decl
  some (SolidCore.Solidity.Source.ABI.selectorFromSignature signature)

/-- BUG#6: the LIBRARY-qualified signature of a public/external library
    function — canonical type names (`Lib.Mode`, `Lib.S`, `C`) plus the
    ` storage` suffix for storage-pointer params. This is what solc hashes
    for library dispatch/delegatecall selectors. -/
def FunctionDecl.libraryAbiSignature? (structEnv : StructEnv)
    (decl : FunctionDecl) : Option String := do
  match decl.kind with
  | FunctionKind.function => some ()
  | _ => none
  let name ← decl.name
  libraryFunctionSignatureWithLocations? structEnv name
    (decl.params.map Parameter.ty) (decl.params.map Parameter.location)

def FunctionDecl.libraryAbiSelector? (structEnv : StructEnv)
    (decl : FunctionDecl) : Option Word := do
  let signature ← FunctionDecl.libraryAbiSignature? structEnv decl
  some (SolidCore.Solidity.Source.ABI.selectorFromSignature signature)

/-- Overload-unique, collision-free function-table key for an internal-linkage
    call target (function-boundary refactor, R6). `"__internal_" ++ abiSignature`
    (e.g. `"__internal_f(uint256)"`) disambiguates same-named overloads and can
    never collide with a plain entrypoint `FunctionDef.name` (which name-based
    dispatch still requires — see `Contract.findFunctionByName?`). Computed
    identically at the call-site emit (`boundaryCallParts?`) and the
    table-build (`directCoreFunctions?`) from the resolved `FunctionDecl`. -/
def FunctionDecl.internalTableKey? (decl : FunctionDecl) : Option Name := do
  let name ← decl.name
  -- Stage E: the key must be TOTAL over named functions — callees whose
  -- parameter types have no ABI-canonical form (e.g. `mapping(...) storage`
  -- parameters) previously fell back to the inline-splice path, which is now
  -- deleted. When `abiSignature?` fails, the name + the structural identity
  -- suffix below still yield a collision-free key (the suffix alone
  -- distinguishes overloads).
  let sig := (FunctionDecl.abiSignature? decl).getD (name ++ "(?)")
  -- Reference-signature extension: the ABI canonical signature collapses
  -- user-defined types — every one-field struct renders `(uint256)`, every enum
  -- `uint8`, every user type `address` (`Ty.abiCanonical?`). Two overloads whose
  -- parameters differ only by such a type (e.g. `div_(Exp memory,Exp memory)`
  -- scaled by 1e18 vs `div_(Double memory,Double memory)` scaled by 1e36, both
  -- `(uint256)` in ABI form) would then share a table key and misdispatch. Append
  -- a structural identity of the parameter types (derived `repr`, which preserves
  -- struct `Path`, enum tag, and user `Path`) so the key is unique per resolved
  -- callee. Computed identically at the call-site emit and the table build (both
  -- from the same resolved `FunctionDecl`), so the two never drift.
  let identity := toString (repr (decl.params.map Parameter.ty))
  some ("__internal_" ++ sig ++ "#" ++ identity)

/-- A parameter/return that the function boundary can carry across a framed
    internal call. Stack values (no data location), `memory` references (the
    memory pointer flows — callee mutations alias back), and `storage` references
    (the storage pointer flows as a plain runtime argument — solc's model) all
    qualify. Excluded: `calldata` references (not yet represented as flowing
    runtime values — kept on the inline-splice path) and function-typed
    parameters/returns (no internal-function-pointer `Value` exists yet). -/
def Parameter.isBoundaryLocation (param : Parameter) : Bool :=
  match param.location with
  | some DataLocation.calldata =>
      -- Stage D (boundary-completion arc): calldata references cross the
      -- boundary too. solc via-IR passes them as plain (offset, length) /
      -- offset descriptor words (docs/refs-completion-solc-research.md §3);
      -- this semantics materializes calldata into immutable `Value`s at the
      -- ABI boundary, and passing an immutable value is observationally
      -- identical to passing a read-only descriptor (calldata cannot be
      -- written, so no aliasing is observable). Slices are value slices.
      true
  | _ => true

/-- A RETURN the function boundary can carry. Stage A of the boundary-completion
    arc: `storage`-ref returns are carried as flowing `Value.storageRef` pointer
    values — solc via-IR returns exactly one word (the slot) from an internal
    `T storage`-returning function and the caller binds it as a plain local
    (`docs/refs-completion-solc-research.md` §1). The callee's named storage
    return is re-declared as a storage alias in the body prologue
    (`toCoreStorageReturnAliasStmts?`), the reference-preserving return
    collection carries the pointer out, and `assignNamedValuesRef?` re-points the
    caller's alias temp. Same exclusions as `isBoundaryLocation` otherwise. -/
def Parameter.isBoundaryReturnLocation (param : Parameter) : Bool :=
  Parameter.isBoundaryLocation param

/-- A callee eligible for the function-boundary (`Stmt.internalCall`)
    representation. Originally (stages 2–3) restricted to pure stack-value
    signatures; the reference-signature extension widens it to callees whose
    parameters and returns are all boundary-carryable
    (`Parameter.isBoundaryLocation`): value, `memory`-ref, and `storage`-ref
    signatures. The `internalTableKey?` guard (an ABI-canonical signature exists)
    additionally excludes anything without an ABI shape. Reference parameters
    flow as pointer VALUES: the arg site lowers them to reference-preserving
    temps (`storageAlias*` / aliasing `memoryVarDecl`) and the interpreter's
    `internalCall` arm binds them reference-preservingly into the callee frame,
    the callee body resolving them through the shared `state`. Synthetic helpers
    (library `__library_*`, `super`/base helpers — mangled, overload-unique
    names) qualify too. Calldata-ref and function-typed callees keep the
    inline-splice path (recorded residue). -/
def FunctionDecl.isBoundaryCallee (decl : FunctionDecl) : Bool :=
  (FunctionDecl.internalTableKey? decl).isSome &&
    decl.params.all Parameter.isBoundaryLocation &&
    decl.returns.all Parameter.isBoundaryReturnLocation

def FunctionDecl.selectorEntry? (decl : FunctionDecl) :
    Option (Name × Word) := do
  let name ← decl.name
  let selector ← FunctionDecl.abiSelector? decl
  some (name, selector)

def ErrorDecl.abiSignature? (decl : ErrorDecl) : Option String := do
  let paramTypes ← Parameters.abiCanonicalTypes? decl.params
  some (decl.name ++ "(" ++ joinStringsWith "," paramTypes ++ ")")

def ErrorDecl.abiSelector? (decl : ErrorDecl) : Option Word := do
  let signature ← ErrorDecl.abiSignature? decl
  some (SolidCore.Solidity.Source.ABI.selectorFromSignature signature)

def ErrorDecl.selectorEntry? (decl : ErrorDecl) :
    Option (Name × Word) := do
  let selector ← ErrorDecl.abiSelector? decl
  some (decl.name, selector)

def EventDecl.abiSignature? (decl : EventDecl) : Option String := do
  let paramTypes ←
    mapOption (fun param => Ty.abiCanonical? param.ty) decl.params
  some (decl.name ++ "(" ++ joinStringsWith "," paramTypes ++ ")")

def EventDecl.abiSelector? (decl : EventDecl) : Option Word := do
  let signature ← EventDecl.abiSignature? decl
  some (SolidCore.Solidity.Source.Keccak.digestWord signature)

def EventDecl.selectorEntry? (decl : EventDecl) :
    Option (Name × Word) := do
  if decl.anonymous then
    none
  else
    let selector ← EventDecl.abiSelector? decl
    some (decl.name, selector)

def StateVarDecl.publicGetterSignature? (decl : StateVarDecl) :
    Option String :=
  match decl.visibility with
  | some Visibility.public_ => do
      let shape ← Ty.publicGetterShape? 64 decl.ty
      let canonical ← mapOption Ty.abiCanonical? shape.fst
      some (decl.name ++ "(" ++ joinStringsWith "," canonical ++ ")")
  | _ => none

def StateVarDecl.selectorEntry? (decl : StateVarDecl) :
    Option (Name × Word) := do
  let signature ← StateVarDecl.publicGetterSignature? decl
  some
    ( decl.name
    , SolidCore.Solidity.Source.ABI.selectorFromSignature signature )

abbrev SelectorEnv := List (Name × Word)

/-- Remove only unqualified declaration names shadowed by lexical binders.
    Qualified entries such as `Base.f` remain available inside the scope. -/
def SelectorEnv.withoutBoundNames (env : SelectorEnv)
    (bound : List Name) : SelectorEnv :=
  env.filter (fun entry => !bound.contains entry.1)

def VarBindings.selectorBoundNames (bindings : List VarBinding) : List Name :=
  bindings.filterMap (fun binding => binding.name)

def Parameters.selectorBoundNames (params : List Parameter) : List Name :=
  params.filterMap (fun param => param.name)

def selectorQualifiedName (contractName functionName : Name) : Name :=
  contractName ++ "." ++ functionName

def FunctionDecl.qualifiedSelectorEntry? (contractName : Name)
    (decl : FunctionDecl) : Option (Name × Word) := do
  let name ← decl.name
  let selector ← FunctionDecl.abiSelector? decl
  some (selectorQualifiedName contractName name, selector)

def SelectorEnv.lookupCompatibleLoop? (query : Name) :
    Option Word -> SelectorEnv -> Option (Option Word)
  | seen?, [] => some seen?
  | seen?, (name, selector) :: rest =>
      if name == query then
        match seen? with
        | none => SelectorEnv.lookupCompatibleLoop? query (some selector) rest
        | some seen =>
            if SolidCore.Solidity.Source.wordEq seen selector then
              SelectorEnv.lookupCompatibleLoop? query seen? rest
            else
              none
      else
        SelectorEnv.lookupCompatibleLoop? query seen? rest

def SelectorEnv.lookup? (env : SelectorEnv) (query : Name) :
    Option Word := do
  let result ← SelectorEnv.lookupCompatibleLoop? query none env
  result

def FunctionDecls.selectorEntries (decls : List FunctionDecl) :
    SelectorEnv :=
  decls.filterMap FunctionDecl.selectorEntry?

def FunctionDecls.qualifiedSelectorEntries
    (contractName : Name) (decls : List FunctionDecl) : SelectorEnv :=
  decls.filterMap (FunctionDecl.qualifiedSelectorEntry? contractName)

/-- BUG#6: `L.f.selector` for a public/external LIBRARY function resolves to
    the library-qualified selector (`keccak("isOff(Lib.Mode)")`), not the
    external-ABI one. Same `Lib.f` env key as the contract entries. -/
def FunctionDecl.libraryQualifiedSelectorEntry? (structEnv : StructEnv)
    (contractName : Name) (decl : FunctionDecl) : Option (Name × Word) := do
  let name ← decl.name
  let selector ← FunctionDecl.libraryAbiSelector? structEnv decl
  some (selectorQualifiedName contractName name, selector)

def FunctionDecls.libraryQualifiedSelectorEntries (structEnv : StructEnv)
    (contractName : Name) (decls : List FunctionDecl) : SelectorEnv :=
  decls.filterMap
    (FunctionDecl.libraryQualifiedSelectorEntry? structEnv contractName)

def ErrorDecls.selectorEntries (decls : List ErrorDecl) :
    SelectorEnv :=
  decls.filterMap ErrorDecl.selectorEntry?

/-- ERROR-SELECTOR-COLLISION (#139 `.selector`): selector entry keyed by the
    `Contract.Bad` joined name (via `selectorQualifiedName`), so a type-qualified
    `L.Bad.selector` / `Base.Bad.selector` resolves to the DECLARING scope's
    selector even under a same-name collision — mirroring the qualified FUNCTION
    and EVENT selector entries. -/
def ErrorDecl.qualifiedSelectorEntry? (contractName : Name)
    (decl : ErrorDecl) : Option (Name × Word) := do
  let (name, selector) ← ErrorDecl.selectorEntry? decl
  some (selectorQualifiedName contractName name, selector)

def ErrorDecls.qualifiedSelectorEntries
    (contractName : Name) (decls : List ErrorDecl) : SelectorEnv :=
  decls.filterMap (ErrorDecl.qualifiedSelectorEntry? contractName)

def StateVarDecls.selectorEntries (decls : List StateVarDecl) :
    SelectorEnv :=
  decls.filterMap StateVarDecl.selectorEntry?

abbrev EventSelectorEnv := List (Name × Word)

def EventDecls.selectorEntries (decls : List EventDecl) :
    EventSelectorEnv :=
  decls.filterMap EventDecl.selectorEntry?

/-- QUALIFIED EVENT SELECTOR (#137 `.selector`): topic0 entry keyed by the
    `Contract.Ev` joined name (via `selectorQualifiedName`), so a type-qualified
    `Base.Ev.selector` / `L.Ping.selector` resolves to the DECLARING scope's
    topic0 even under a same-name collision — mirroring the qualified FUNCTION
    selector entries. -/
def EventDecl.qualifiedSelectorEntry? (contractName : Name)
    (decl : EventDecl) : Option (Name × Word) := do
  let (name, selector) ← EventDecl.selectorEntry? decl
  some (selectorQualifiedName contractName name, selector)

def EventDecls.qualifiedSelectorEntries
    (contractName : Name) (decls : List EventDecl) : EventSelectorEnv :=
  decls.filterMap (EventDecl.qualifiedSelectorEntry? contractName)

def EventSelectorEnv.lookup? (env : EventSelectorEnv) (query : Name) :
    Option Word :=
  SelectorEnv.lookup? env query

def EventSelectorEnv.withoutBoundNames (env : EventSelectorEnv)
    (bound : List Name) : EventSelectorEnv :=
  SelectorEnv.withoutBoundNames env bound

def selectorLiteralExpr (selector : Word) : Expr :=
  Expr.call (Expr.typeName (Ty.bytesN 4))
    [ Arg.positional
        (Expr.literal
          (Literal.bytes
            (SolidCore.Solidity.Source.wordToBytesBE
              SolidCore.Solidity.Source.selectorBytes selector))) ]

def eventSelectorLiteralExpr (selector : Word) : Expr :=
  Expr.call (Expr.typeName (Ty.bytesN 32))
    [ Arg.positional
        (Expr.literal
          (Literal.bytes
            (SolidCore.Solidity.Source.wordToBytesBE
              SolidCore.Solidity.Source.wordBytes selector))) ]

def FunctionDecls.interfaceId? : List FunctionDecl -> Option Word
  | [] => some 0
  | decl :: rest => do
      let selector ← FunctionDecl.abiSelector? decl
      let tail ← FunctionDecls.interfaceId? rest
      some (SolidCore.Solidity.Shared.xorWord selector tail)

abbrev InterfaceIdEnv := List (Name × Word)

def InterfaceIdEnv.lookup? : InterfaceIdEnv -> Name -> Option Word
  | [], _ => none
  | (name, interfaceId) :: rest, query =>
      if name == query then
        some interfaceId
      else
        InterfaceIdEnv.lookup? rest query

def interfaceIdLiteralExpr (interfaceId : Word) : Expr :=
  Expr.call (Expr.typeName (Ty.bytesN 4))
    [ Arg.positional
        (Expr.literal
          (Literal.bytes
            (SolidCore.Solidity.Source.wordToBytesBE
              SolidCore.Solidity.Source.selectorBytes interfaceId))) ]

mutual

def Expr.resolveInterfaceIdsFuel : Nat -> InterfaceIdEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let resolve := Expr.resolveInterfaceIdsFuel fuel env
      let resolveArg := Arg.resolveInterfaceIdsFuel fuel env
      let resolveOption := CallOption.resolveInterfaceIdsFuel fuel env
      let resolveTupleItem := TupleItem.resolveInterfaceIdsFuel fuel env
      match expr with
      | Expr.member (Expr.typeName (Ty.user path)) "interfaceId" =>
          match pathLast? path with
          | some name =>
              match InterfaceIdEnv.lookup? env name with
              | some interfaceId => interfaceIdLiteralExpr interfaceId
              | none => expr
          | none => expr
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs =>
          Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveInterfaceIdsFuel :
    Nat -> InterfaceIdEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, env, arg =>
      let resolve := Expr.resolveInterfaceIdsFuel fuel env
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveInterfaceIdsFuel :
    Nat -> InterfaceIdEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, env, option =>
      let resolve := Expr.resolveInterfaceIdsFuel fuel env
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveInterfaceIdsFuel :
    Nat -> InterfaceIdEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | fuel + 1, env, item =>
      let resolve := Expr.resolveInterfaceIdsFuel fuel env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def defaultResolveInterfaceIdsFuel : Nat := 1024

def Expr.resolveInterfaceIds (env : InterfaceIdEnv) (expr : Expr) : Expr :=
  Expr.resolveInterfaceIdsFuel defaultResolveInterfaceIdsFuel env expr

def Arg.resolveInterfaceIds (env : InterfaceIdEnv) (arg : Arg) : Arg :=
  Arg.resolveInterfaceIdsFuel defaultResolveInterfaceIdsFuel env arg

def ModifierInvocation.resolveInterfaceIds (env : InterfaceIdEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with args := invocation.args.map (Arg.resolveInterfaceIds env) }

def StateVarDecl.resolveInterfaceIds (env : InterfaceIdEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with init := decl.init.map (Expr.resolveInterfaceIds env) }

mutual

def Stmt.resolveInterfaceIdsFuel : Nat -> InterfaceIdEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, env, stmt =>
      let resolveStmt := Stmt.resolveInterfaceIdsFuel fuel env
      let resolveExpr := Expr.resolveInterfaceIdsFuel fuel env
      let resolveClause := CatchClause.resolveInterfaceIdsFuel fuel env
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map resolveStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map resolveExpr)
      | Stmt.expr expr => Stmt.expr (resolveExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (resolveExpr cond) (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) (resolveExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map resolveStmt) (cond.map resolveExpr)
            (post.map resolveExpr) (resolveStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (resolveExpr expr) returns
            (resolveStmt success) (clauses.map resolveClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (resolveExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (resolveExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map resolveExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveInterfaceIdsFuel :
    Nat -> InterfaceIdEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, env, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.resolveInterfaceIdsFuel fuel env body)

end

def Stmt.resolveInterfaceIds (env : InterfaceIdEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveInterfaceIdsFuel defaultResolveInterfaceIdsFuel env stmt

def FunctionDecl.resolveInterfaceIds (env : InterfaceIdEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    modifiers := decl.modifiers.map (ModifierInvocation.resolveInterfaceIds env)
    body := decl.body.map (Stmt.resolveInterfaceIds env) }

def ModifierDecl.resolveInterfaceIds (env : InterfaceIdEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  { decl with body := decl.body.map (Stmt.resolveInterfaceIds env) }

mutual

def Expr.resolveSelectorsFuel :
    Nat -> SelectorEnv -> SelectorEnv -> Expr -> Expr
  | 0, _, _, expr => expr
  | fuel + 1, env, unqualifiedEnv, expr =>
      let resolve := Expr.resolveSelectorsFuel fuel env unqualifiedEnv
      let resolveArg := Arg.resolveSelectorsFuel fuel env unqualifiedEnv
      let resolveOption := CallOption.resolveSelectorsFuel fuel env unqualifiedEnv
      let resolveTupleItem :=
        TupleItem.resolveSelectorsFuel fuel env unqualifiedEnv
      match expr with
      | Expr.member (Expr.ternary cond thenExpr elseExpr) "selector" =>
          -- Select only the chosen function's selector. Resolving each arm
          -- exposes bound function names to the same lookup used by a direct
          -- `this.f.selector`, without requiring env-less lowering of `this.f`.
          Expr.ternary (resolve cond)
            (resolve (Expr.member thenExpr "selector"))
            (resolve (Expr.member elseExpr "selector"))
      | Expr.member (Expr.ident name) "selector" =>
          match SelectorEnv.lookup? unqualifiedEnv name with
          | some selector => selectorLiteralExpr selector
          | none => expr
      | Expr.member
          (Expr.member
            (Expr.typeName (Ty.user path)) name) "selector" =>
          match pathLast? path with
          | some contractName =>
              match
                  SelectorEnv.lookup? env
                    (selectorQualifiedName contractName name) with
              | some selector => selectorLiteralExpr selector
              | none =>
                  match SelectorEnv.lookup? env name with
                  | some selector => selectorLiteralExpr selector
                  | none =>
                      Expr.member
                        (Expr.member (Expr.typeName (Ty.user path)) name)
                        "selector"
          | none =>
              match SelectorEnv.lookup? env name with
              | some selector => selectorLiteralExpr selector
              | none =>
                  Expr.member
                    (Expr.member (Expr.typeName (Ty.user path)) name)
                    "selector"
      | Expr.member (Expr.member base name) "selector" =>
          match SelectorEnv.lookup? env name with
          | some selector => selectorLiteralExpr selector
          | none => Expr.member (Expr.member (resolve base) name) "selector"
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs =>
          Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveSelectorsFuel :
    Nat -> SelectorEnv -> SelectorEnv -> Arg -> Arg
  | 0, _, _, arg => arg
  | fuel + 1, env, unqualifiedEnv, arg =>
      let resolve := Expr.resolveSelectorsFuel fuel env unqualifiedEnv
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveSelectorsFuel :
    Nat -> SelectorEnv -> SelectorEnv -> CallOption -> CallOption
  | 0, _, _, option => option
  | fuel + 1, env, unqualifiedEnv, option =>
      let resolve := Expr.resolveSelectorsFuel fuel env unqualifiedEnv
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveSelectorsFuel :
    Nat -> SelectorEnv -> SelectorEnv -> TupleItem -> TupleItem
  | 0, _, _, item => item
  | fuel + 1, env, unqualifiedEnv, item =>
      let resolve := Expr.resolveSelectorsFuel fuel env unqualifiedEnv
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def defaultResolveSelectorsFuel : Nat := 1024

def Expr.resolveSelectors (env : SelectorEnv) (expr : Expr) : Expr :=
  Expr.resolveSelectorsFuel defaultResolveSelectorsFuel env env expr

def Expr.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv) (expr : Expr) : Expr :=
  Expr.resolveSelectorsFuel defaultResolveSelectorsFuel
    env unqualifiedEnv expr

/-- Find the call-valued receiver of a known function selector when the
    selector is the whole value of a return expression, possibly under a chain
    of single-argument explicit conversions. Extracting the call is safe in
    these shapes because the wrappers have no other operands whose evaluation
    could be reordered. -/
def Expr.selectorReceiverCallUnderCasts? (env : SelectorEnv) : Expr -> Option Expr
  | Expr.member (Expr.member base@(Expr.call _ _) name) "selector" => do
      let _ ← SelectorEnv.lookup? env name
      some base
  | Expr.call (Expr.typeName _) [Arg.positional inner] =>
      Expr.selectorReceiverCallUnderCasts? env inner
  | Expr.payableConversion inner =>
      Expr.selectorReceiverCallUnderCasts? env inner
  | _ => none

def Arg.resolveSelectors (env : SelectorEnv) (arg : Arg) : Arg :=
  Arg.resolveSelectorsFuel defaultResolveSelectorsFuel env env arg

def Arg.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv) (arg : Arg) : Arg :=
  Arg.resolveSelectorsFuel defaultResolveSelectorsFuel
    env unqualifiedEnv arg

def BaseSpecifier.resolveSelectors (env : SelectorEnv)
    (spec : BaseSpecifier) : BaseSpecifier :=
  { spec with args := spec.args.map (Arg.resolveSelectors env) }

def BaseSpecifier.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv) (spec : BaseSpecifier) :
    BaseSpecifier :=
  { spec with
    args :=
      spec.args.map (Arg.resolveSelectorsWithUnqualified env unqualifiedEnv) }

def ModifierInvocation.resolveSelectors (env : SelectorEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with args := invocation.args.map (Arg.resolveSelectors env) }

def ModifierInvocation.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with
    args :=
      invocation.args.map
        (Arg.resolveSelectorsWithUnqualified env unqualifiedEnv) }

def StateVarDecl.resolveSelectors (env : SelectorEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with init := decl.init.map (Expr.resolveSelectors env) }

def StateVarDecl.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv) (decl : StateVarDecl) :
    StateVarDecl :=
  { decl with
    init :=
      decl.init.map
        (Expr.resolveSelectorsWithUnqualified env unqualifiedEnv) }

mutual

def Stmt.resolveSelectorsFuel :
    Nat -> SelectorEnv -> SelectorEnv -> Stmt -> Stmt
  | 0, _, _, stmt => stmt
  | fuel + 1, env, unqualifiedEnv, stmt =>
      let resolveStmt :=
        Stmt.resolveSelectorsFuel fuel env unqualifiedEnv
      let resolveExpr :=
        Expr.resolveSelectorsFuel fuel env unqualifiedEnv
      let resolveClause :=
        CatchClause.resolveSelectorsFuel fuel env unqualifiedEnv
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body =>
          -- Resolve an initializer in the incoming scope, then hide the names
          -- it binds from the declaration-selector tables for later siblings.
          Stmt.block
            ((body.foldl
              (fun (acc : List Stmt × (SelectorEnv × SelectorEnv)) item =>
                let item' :=
                  Stmt.resolveSelectorsFuel fuel acc.2.1 acc.2.2 item
                let bound :=
                  match item with
                  | Stmt.varDecl bindings _ =>
                      VarBindings.selectorBoundNames bindings
                  | _ => []
                ( acc.1 ++ [item']
                , acc.2.1.withoutBoundNames bound
                , acc.2.2.withoutBoundNames bound ))
              ([], env, unqualifiedEnv)).1)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map resolveExpr)
      | Stmt.expr
          (Expr.member (Expr.member base@(Expr.call _ _) name) "selector") =>
          -- Resolving a known selector to a literal must not erase evaluation of
          -- its receiver. In expression-statement position the selector value is
          -- discarded, so preserve the call-valued base for its side effects.
          match SelectorEnv.lookup? env name with
          | some _ => Stmt.expr (resolveExpr base)
          | none =>
              Stmt.expr
                (Expr.member (Expr.member (resolveExpr base) name) "selector")
      | Stmt.expr expr => Stmt.expr (resolveExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (resolveExpr cond) (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) (resolveExpr cond)
      | Stmt.forLoop init cond post body =>
          let bound :=
            match init with
            | some (Stmt.varDecl bindings _) =>
                VarBindings.selectorBoundNames bindings
            | _ => []
          let envIn := env.withoutBoundNames bound
          let unqualifiedIn := unqualifiedEnv.withoutBoundNames bound
          Stmt.forLoop (init.map resolveStmt)
            (cond.map (Expr.resolveSelectorsFuel fuel envIn unqualifiedIn))
            (post.map (Expr.resolveSelectorsFuel fuel envIn unqualifiedIn))
            (Stmt.resolveSelectorsFuel fuel envIn unqualifiedIn body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          let bound := Parameters.selectorBoundNames returns
          let envIn := env.withoutBoundNames bound
          let unqualifiedIn := unqualifiedEnv.withoutBoundNames bound
          Stmt.tryCatchReturns (resolveExpr expr) returns
            (Stmt.resolveSelectorsFuel fuel envIn unqualifiedIn success)
            (clauses.map resolveClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (resolveExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (resolveExpr expr)
      | Stmt.returnValues (some expr) =>
          match Expr.selectorReceiverCallUnderCasts? env expr with
          | some base =>
              -- Selector resolution replaces the selector with a literal. Keep
              -- the call-valued receiver in front of the return so its effects
              -- and failures still occur before the converted selector value.
              Stmt.block
                [Stmt.expr (resolveExpr base),
                 Stmt.returnValues (some (resolveExpr expr))]
          | none => Stmt.returnValues (some (resolveExpr expr))
      | Stmt.returnValues none => Stmt.returnValues none
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveSelectorsFuel :
    Nat -> SelectorEnv -> SelectorEnv -> CatchClause -> CatchClause
  | 0, _, _, clause => clause
  | fuel + 1, env, unqualifiedEnv, clause =>
      match clause with
      | CatchClause.clause name params body =>
          let bound := Parameters.selectorBoundNames params
          CatchClause.clause name params
            (Stmt.resolveSelectorsFuel fuel
              (env.withoutBoundNames bound)
              (unqualifiedEnv.withoutBoundNames bound) body)

end

def Stmt.resolveSelectors (env : SelectorEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveSelectorsFuel defaultResolveSelectorsFuel env env stmt

def Stmt.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveSelectorsFuel defaultResolveSelectorsFuel
    env unqualifiedEnv stmt

def FunctionDecl.resolveSelectors (env : SelectorEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  let bound :=
    Parameters.selectorBoundNames decl.params ++
      Parameters.selectorBoundNames decl.returns
  let envIn := env.withoutBoundNames bound
  { decl with
    modifiers := decl.modifiers.map (ModifierInvocation.resolveSelectors envIn)
    body := decl.body.map (Stmt.resolveSelectors envIn) }

def FunctionDecl.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv) (decl : FunctionDecl) :
    FunctionDecl :=
  let bound :=
    Parameters.selectorBoundNames decl.params ++
      Parameters.selectorBoundNames decl.returns
  let envIn := env.withoutBoundNames bound
  let unqualifiedIn := unqualifiedEnv.withoutBoundNames bound
  { decl with
    modifiers :=
      decl.modifiers.map
        (ModifierInvocation.resolveSelectorsWithUnqualified
          envIn unqualifiedIn)
    body :=
      decl.body.map (Stmt.resolveSelectorsWithUnqualified envIn unqualifiedIn) }

def ModifierDecl.resolveSelectors (env : SelectorEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  let envIn :=
    env.withoutBoundNames (Parameters.selectorBoundNames decl.params)
  { decl with body := decl.body.map (Stmt.resolveSelectors envIn) }

def ModifierDecl.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv) (decl : ModifierDecl) :
    ModifierDecl :=
  let bound := Parameters.selectorBoundNames decl.params
  let envIn := env.withoutBoundNames bound
  let unqualifiedIn := unqualifiedEnv.withoutBoundNames bound
  { decl with
    body :=
      decl.body.map
        (Stmt.resolveSelectorsWithUnqualified envIn unqualifiedIn) }

def ContractItem.resolveSelectors (env : SelectorEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveSelectors env decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.resolveSelectors env decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.resolveSelectors env decl)
  | other => other

def ContractItem.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar
        (StateVarDecl.resolveSelectorsWithUnqualified env unqualifiedEnv decl)
  | ContractItem.function decl =>
      ContractItem.function
        (FunctionDecl.resolveSelectorsWithUnqualified env unqualifiedEnv decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl
        (ModifierDecl.resolveSelectorsWithUnqualified env unqualifiedEnv decl)
  | other => other

def ContractDecl.resolveSelectors (env : SelectorEnv)
    (decl : ContractDecl) : ContractDecl :=
  { decl with
    layoutBase := decl.layoutBase.map (Expr.resolveSelectors env)
    bases := decl.bases.map (BaseSpecifier.resolveSelectors env)
    items := decl.items.map (ContractItem.resolveSelectors env) }

def ContractDecl.resolveSelectorsWithUnqualified
    (env unqualifiedEnv : SelectorEnv) (decl : ContractDecl) :
    ContractDecl :=
  { decl with
    layoutBase :=
      decl.layoutBase.map
        (Expr.resolveSelectorsWithUnqualified env unqualifiedEnv)
    bases :=
      decl.bases.map
        (BaseSpecifier.resolveSelectorsWithUnqualified env unqualifiedEnv)
    items :=
      decl.items.map
        (ContractItem.resolveSelectorsWithUnqualified env unqualifiedEnv) }

mutual

def Expr.resolveEventSelectorsFuel :
    Nat -> EventSelectorEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let resolve := Expr.resolveEventSelectorsFuel fuel env
      let resolveArg := Arg.resolveEventSelectorsFuel fuel env
      let resolveOption := CallOption.resolveEventSelectorsFuel fuel env
      let resolveTupleItem := TupleItem.resolveEventSelectorsFuel fuel env
      match expr with
      | Expr.member (Expr.ident name) "selector" =>
          match EventSelectorEnv.lookup? env name with
          | some selector => eventSelectorLiteralExpr selector
          | none => expr
      -- QUALIFIED EVENT SELECTOR (#137 `.selector`): `Base.Ev.selector`,
      -- `L.Ping.selector`. Resolve the DECLARING scope's topic0 by the joined
      -- `Contract.Ev` key first (so a name collision with the contract's own
      -- event does not mis-target), falling back to the bare name — mirroring the
      -- qualified error/function selector arm.
      | Expr.member
          (Expr.member (Expr.typeName (Ty.user path)) name) "selector" =>
          match pathLast? path with
          | some contractName =>
              match
                  EventSelectorEnv.lookup? env
                    (selectorQualifiedName contractName name) with
              | some selector => eventSelectorLiteralExpr selector
              | none =>
                  match EventSelectorEnv.lookup? env name with
                  | some selector => eventSelectorLiteralExpr selector
                  | none =>
                      Expr.member
                        (Expr.member (Expr.typeName (Ty.user path)) name)
                        "selector"
          | none =>
              match EventSelectorEnv.lookup? env name with
              | some selector => eventSelectorLiteralExpr selector
              | none =>
                  Expr.member
                    (Expr.member (Expr.typeName (Ty.user path)) name)
                    "selector"
      | Expr.member (Expr.member base name) "selector" =>
          match EventSelectorEnv.lookup? env name with
          | some selector => eventSelectorLiteralExpr selector
          | none => Expr.member (Expr.member (resolve base) name) "selector"
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs =>
          Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveEventSelectorsFuel :
    Nat -> EventSelectorEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, env, arg =>
      let resolve := Expr.resolveEventSelectorsFuel fuel env
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveEventSelectorsFuel :
    Nat -> EventSelectorEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, env, option =>
      let resolve := Expr.resolveEventSelectorsFuel fuel env
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveEventSelectorsFuel :
    Nat -> EventSelectorEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | fuel + 1, env, item =>
      let resolve := Expr.resolveEventSelectorsFuel fuel env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def Expr.resolveEventSelectors
    (env : EventSelectorEnv) (expr : Expr) : Expr :=
  Expr.resolveEventSelectorsFuel defaultResolveSelectorsFuel env expr

def Arg.resolveEventSelectors
    (env : EventSelectorEnv) (arg : Arg) : Arg :=
  Arg.resolveEventSelectorsFuel defaultResolveSelectorsFuel env arg

def BaseSpecifier.resolveEventSelectors
    (env : EventSelectorEnv) (spec : BaseSpecifier) : BaseSpecifier :=
  { spec with args := spec.args.map (Arg.resolveEventSelectors env) }

def ModifierInvocation.resolveEventSelectors
    (env : EventSelectorEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with
    args := invocation.args.map (Arg.resolveEventSelectors env) }

def StateVarDecl.resolveEventSelectors
    (env : EventSelectorEnv) (decl : StateVarDecl) : StateVarDecl :=
  { decl with init := decl.init.map (Expr.resolveEventSelectors env) }

mutual

def Stmt.resolveEventSelectorsFuel :
    Nat -> EventSelectorEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, env, stmt =>
      let resolveStmt := Stmt.resolveEventSelectorsFuel fuel env
      let resolveExpr := Expr.resolveEventSelectorsFuel fuel env
      let resolveClause := CatchClause.resolveEventSelectorsFuel fuel env
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body =>
          Stmt.block
            ((body.foldl
              (fun (acc : List Stmt × EventSelectorEnv) item =>
                let item' :=
                  Stmt.resolveEventSelectorsFuel fuel acc.2 item
                let bound :=
                  match item with
                  | Stmt.varDecl bindings _ =>
                      VarBindings.selectorBoundNames bindings
                  | _ => []
                (acc.1 ++ [item'], acc.2.withoutBoundNames bound))
              ([], env)).1)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map resolveExpr)
      | Stmt.expr expr => Stmt.expr (resolveExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (resolveExpr cond) (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) (resolveExpr cond)
      | Stmt.forLoop init cond post body =>
          let bound :=
            match init with
            | some (Stmt.varDecl bindings _) =>
                VarBindings.selectorBoundNames bindings
            | _ => []
          let envIn := env.withoutBoundNames bound
          Stmt.forLoop (init.map resolveStmt)
            (cond.map (Expr.resolveEventSelectorsFuel fuel envIn))
            (post.map (Expr.resolveEventSelectorsFuel fuel envIn))
            (Stmt.resolveEventSelectorsFuel fuel envIn body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          let envIn :=
            env.withoutBoundNames (Parameters.selectorBoundNames returns)
          Stmt.tryCatchReturns (resolveExpr expr) returns
            (Stmt.resolveEventSelectorsFuel fuel envIn success)
            (clauses.map resolveClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (resolveExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (resolveExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map resolveExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveEventSelectorsFuel :
    Nat -> EventSelectorEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, env, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.resolveEventSelectorsFuel fuel
              (env.withoutBoundNames (Parameters.selectorBoundNames params))
              body)

end

def Stmt.resolveEventSelectors
    (env : EventSelectorEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveEventSelectorsFuel defaultResolveSelectorsFuel env stmt

def FunctionDecl.resolveEventSelectors
    (env : EventSelectorEnv) (decl : FunctionDecl) : FunctionDecl :=
  let bound :=
    Parameters.selectorBoundNames decl.params ++
      Parameters.selectorBoundNames decl.returns
  let envIn := env.withoutBoundNames bound
  { decl with
    modifiers := decl.modifiers.map
      (ModifierInvocation.resolveEventSelectors envIn)
    body := decl.body.map (Stmt.resolveEventSelectors envIn) }

def ModifierDecl.resolveEventSelectors
    (env : EventSelectorEnv) (decl : ModifierDecl) : ModifierDecl :=
  let envIn :=
    env.withoutBoundNames (Parameters.selectorBoundNames decl.params)
  { decl with body := decl.body.map (Stmt.resolveEventSelectors envIn) }

def ContractItem.resolveEventSelectors
    (env : EventSelectorEnv) : ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveEventSelectors env decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.resolveEventSelectors env decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.resolveEventSelectors env decl)
  | other => other

def ContractDecl.resolveEventSelectors
    (env : EventSelectorEnv) (decl : ContractDecl) : ContractDecl :=
  { decl with
    layoutBase := decl.layoutBase.map (Expr.resolveEventSelectors env)
    bases := decl.bases.map (BaseSpecifier.resolveEventSelectors env)
    items := decl.items.map (ContractItem.resolveEventSelectors env) }

mutual

def Expr.resolveFunctionAddressesFuel : Nat -> SelectorEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let resolve := Expr.resolveFunctionAddressesFuel fuel env
      let resolveArg := Arg.resolveFunctionAddressesFuel fuel env
      let resolveOption := CallOption.resolveFunctionAddressesFuel fuel env
      let resolveTupleItem := TupleItem.resolveFunctionAddressesFuel fuel env
      match expr with
      | Expr.member (Expr.ternary cond thenExpr elseExpr) "address" =>
          -- Address projection distributes over an external-function-value
          -- ternary just like selector projection does.  Resolving each arm
          -- first turns `this.f.address` / `this.g.address` into `this`, while
          -- retaining the chosen condition and its source-width checks.
          Expr.ternary (resolve cond)
            (resolve (Expr.member thenExpr "address"))
            (resolve (Expr.member elseExpr "address"))
      | Expr.member (Expr.member base _) "address" => resolve base
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs =>
          Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, env, arg =>
      let resolve := Expr.resolveFunctionAddressesFuel fuel env
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, env, option =>
      let resolve := Expr.resolveFunctionAddressesFuel fuel env
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | fuel + 1, env, item =>
      let resolve := Expr.resolveFunctionAddressesFuel fuel env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def defaultResolveFunctionAddressesFuel : Nat := 1024

def Expr.resolveFunctionAddresses (env : SelectorEnv) (expr : Expr) : Expr :=
  Expr.resolveFunctionAddressesFuel
    defaultResolveFunctionAddressesFuel env expr

def Arg.resolveFunctionAddresses (env : SelectorEnv) (arg : Arg) : Arg :=
  Arg.resolveFunctionAddressesFuel defaultResolveFunctionAddressesFuel env arg

def BaseSpecifier.resolveFunctionAddresses (env : SelectorEnv)
    (spec : BaseSpecifier) : BaseSpecifier :=
  { spec with args := spec.args.map (Arg.resolveFunctionAddresses env) }

def ModifierInvocation.resolveFunctionAddresses (env : SelectorEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with
    args := invocation.args.map (Arg.resolveFunctionAddresses env) }

def StateVarDecl.resolveFunctionAddresses (env : SelectorEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with init := decl.init.map (Expr.resolveFunctionAddresses env) }

mutual

def Stmt.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, env, stmt =>
      let resolveStmt := Stmt.resolveFunctionAddressesFuel fuel env
      let resolveExpr := Expr.resolveFunctionAddressesFuel fuel env
      let resolveClause := CatchClause.resolveFunctionAddressesFuel fuel env
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map resolveStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map resolveExpr)
      | Stmt.expr expr => Stmt.expr (resolveExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (resolveExpr cond) (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) (resolveExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map resolveStmt) (cond.map resolveExpr)
            (post.map resolveExpr) (resolveStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (resolveExpr expr) returns
            (resolveStmt success) (clauses.map resolveClause)
      | Stmt.emitEvent expr => (Stmt.emitEvent (resolveExpr expr))
      | Stmt.revertCall expr => (Stmt.revertCall (resolveExpr expr))
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map resolveExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, env, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.resolveFunctionAddressesFuel fuel env body)

end

def Stmt.resolveFunctionAddresses (env : SelectorEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveFunctionAddressesFuel
    defaultResolveFunctionAddressesFuel env stmt

def FunctionDecl.resolveFunctionAddresses (env : SelectorEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    modifiers :=
      decl.modifiers.map (ModifierInvocation.resolveFunctionAddresses env)
    body := decl.body.map (Stmt.resolveFunctionAddresses env) }

def ModifierDecl.resolveFunctionAddresses (env : SelectorEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  { decl with body := decl.body.map (Stmt.resolveFunctionAddresses env) }

def ContractItem.resolveFunctionAddresses (env : SelectorEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveFunctionAddresses env decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.resolveFunctionAddresses env decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.resolveFunctionAddresses env decl)
  | other => other

def ContractDecl.resolveFunctionAddresses (env : SelectorEnv)
    (decl : ContractDecl) : ContractDecl :=
  { decl with
    layoutBase := decl.layoutBase.map (Expr.resolveFunctionAddresses env)
    bases := decl.bases.map (BaseSpecifier.resolveFunctionAddresses env)
    items := decl.items.map (ContractItem.resolveFunctionAddresses env) }

def Args.toArgsForParamNames? (paramNames : List (Option Name))
    (args : List Arg) : Option (List Arg) := do
  let exprs ← Args.toExprsForParamNames? paramNames args
  some (exprs.map Arg.positional)

abbrev NamedArgParamEnv := List (Name × List (Option Name))

def NamedArgParamEnv.orderArgs? (env : NamedArgParamEnv)
    (target : Name) (args : List Arg) : Option (List Arg) :=
  match env with
  | [] => none
  | (name, paramNames) :: rest =>
      if name == target then
        match Args.toArgsForParamNames? paramNames args with
        | some ordered => some ordered
        | none => NamedArgParamEnv.orderArgs? rest target args
      else
        NamedArgParamEnv.orderArgs? rest target args

def EventDecl.paramNames (decl : EventDecl) : List (Option Name) :=
  decl.params.map EventParam.name

def ErrorDecl.paramNames (decl : ErrorDecl) : List (Option Name) :=
  decl.params.map Parameter.name

def EventDecl.namedArgEntry (decl : EventDecl) :
    Name × List (Option Name) :=
  (decl.name, EventDecl.paramNames decl)

def ErrorDecl.namedArgEntry (decl : ErrorDecl) :
    Name × List (Option Name) :=
  (decl.name, ErrorDecl.paramNames decl)

def EventDecls.namedArgEnv (decls : List EventDecl) :
    NamedArgParamEnv :=
  decls.map EventDecl.namedArgEntry

/-- STAGE-D #195: per-event positional `indexed` flags, keyed by event name.
    Threaded into the ANF emit-arg hoister so `emit E(f(), g(), …)` binds its
    call-argument temps in solc's TWO-PHASE order (indexed/topic args in REVERSE
    source order first, then non-indexed/data args in FORWARD source order —
    `ExpressionCompiler.cpp` `Kind::Event`), matching the interpreter's two-phase
    emit schedule (R1) which is otherwise DEAD for call args pre-evaluated L2R. -/
abbrev EventIndexedEnv := List (Name × List Bool)

def EventDecls.indexedEnv (decls : List EventDecl) : EventIndexedEnv :=
  decls.map (fun decl => (decl.name, decl.params.map (fun p => p.indexed)))

def ErrorDecls.namedArgEnv (decls : List ErrorDecl) :
    NamedArgParamEnv :=
  decls.map ErrorDecl.namedArgEntry

def EventDecls.withoutNamesOf (locals : List EventDecl) :
    List EventDecl -> List EventDecl
  | [] => []
  | decl :: rest =>
      if locals.any (fun localDecl => localDecl.name == decl.name) then
        EventDecls.withoutNamesOf locals rest
      else
        decl :: EventDecls.withoutNamesOf locals rest

def ErrorDecls.withoutNamesOf (locals : List ErrorDecl) :
    List ErrorDecl -> List ErrorDecl
  | [] => []
  | decl :: rest =>
      if locals.any (fun localDecl => localDecl.name == decl.name) then
        ErrorDecls.withoutNamesOf locals rest
      else
        decl :: ErrorDecls.withoutNamesOf locals rest

mutual

def Stmt.resolveNamedEventErrorArgsFuel :
    Nat -> NamedArgParamEnv -> NamedArgParamEnv -> Stmt -> Stmt
  | 0, _, _, stmt => stmt
  | fuel + 1, eventEnv, errorEnv, stmt =>
      let resolveStmt :=
        Stmt.resolveNamedEventErrorArgsFuel fuel eventEnv errorEnv
      let resolveClause :=
        CatchClause.resolveNamedEventErrorArgsFuel fuel eventEnv errorEnv
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map resolveStmt)
      | Stmt.varDecl bindings init => Stmt.varDecl bindings init
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [ Arg.positional cond
            , Arg.positional (Expr.call (Expr.ident name) args) ]) =>
          match NamedArgParamEnv.orderArgs? errorEnv name args with
          | some ordered =>
              Stmt.expr
                (Expr.call (Expr.ident "require")
                  [ Arg.positional cond
                  , Arg.positional (Expr.call (Expr.ident name) ordered) ])
          | none =>
              Stmt.expr
                (Expr.call (Expr.ident "require")
                  [ Arg.positional cond
                  , Arg.positional (Expr.call (Expr.ident name) args) ])
      | Stmt.expr expr => Stmt.expr expr
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse cond (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop cond (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) cond
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map resolveStmt) cond post (resolveStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch expr (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns expr returns
            (resolveStmt success) (clauses.map resolveClause)
      | Stmt.emitEvent (Expr.call (Expr.ident name) args) =>
          match NamedArgParamEnv.orderArgs? eventEnv name args with
          | some ordered =>
              Stmt.emitEvent (Expr.call (Expr.ident name) ordered)
          | none => Stmt.emitEvent (Expr.call (Expr.ident name) args)
      | Stmt.emitEvent expr => Stmt.emitEvent expr
      | Stmt.revertCall (Expr.call (Expr.ident name) args) =>
          match NamedArgParamEnv.orderArgs? errorEnv name args with
          | some ordered =>
              Stmt.revertCall (Expr.call (Expr.ident name) ordered)
          | none => Stmt.revertCall (Expr.call (Expr.ident name) args)
      | Stmt.revertCall expr => Stmt.revertCall expr
      | Stmt.returnValues expr? => Stmt.returnValues expr?
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveNamedEventErrorArgsFuel :
    Nat -> NamedArgParamEnv -> NamedArgParamEnv -> CatchClause -> CatchClause
  | 0, _, _, clause => clause
  | fuel + 1, eventEnv, errorEnv, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.resolveNamedEventErrorArgsFuel fuel eventEnv errorEnv body)

end

def Stmt.resolveNamedEventErrorArgs
    (eventEnv errorEnv : NamedArgParamEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveNamedEventErrorArgsFuel defaultResolveInterfaceIdsFuel
    eventEnv errorEnv stmt

/-- QUALIFIED-COLLISION (#136/#137): rewrite a TYPE-qualified emit/revert/require
    error/event callee `X.M` to a bare identifier carrying the `.`-joined
    `qualifiedConstantKey X.M` — but ONLY when `M` is an AMBIGUOUS name (a
    library member whose bare name also names a differently-signed contract
    member, so the by-name runtime table would mis-target). Non-ambiguous
    qualified callees are left as member accesses and lower to the bare name
    exactly as before (byte-identical). solc forbids a derived contract from
    redeclaring an inherited event/error name, so base- or self-qualified
    callees are never ambiguous and are never rewritten. -/
def Expr.qualifyCollidingCallee (colliding : List Name) : Expr -> Expr
  | Expr.call (Expr.member (Expr.typeName (Ty.user path)) name) args =>
      if colliding.contains name then
        Expr.call (Expr.ident (qualifiedConstantKey path name)) args
      else
        Expr.call (Expr.member (Expr.typeName (Ty.user path)) name) args
  | other => other

mutual

def Stmt.qualifyCollidingEventErrorsFuel :
    Nat -> List Name -> List Name -> Stmt -> Stmt
  | 0, _, _, stmt => stmt
  | fuel + 1, collidingEvents, collidingErrors, stmt =>
      let recStmt :=
        Stmt.qualifyCollidingEventErrorsFuel fuel collidingEvents collidingErrors
      let recClause :=
        CatchClause.qualifyCollidingEventErrorsFuel fuel collidingEvents
          collidingErrors
      match stmt with
      | Stmt.block body => Stmt.block (body.map recStmt)
      | Stmt.emitEvent expr =>
          Stmt.emitEvent (Expr.qualifyCollidingCallee collidingEvents expr)
      | Stmt.revertCall expr =>
          Stmt.revertCall (Expr.qualifyCollidingCallee collidingErrors expr)
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [ Arg.positional cond, Arg.positional errCall ]) =>
          Stmt.expr
            (Expr.call (Expr.ident "require")
              [ Arg.positional cond
              , Arg.positional
                  (Expr.qualifyCollidingCallee collidingErrors errCall) ])
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse cond (recStmt thenBranch) (elseBranch.map recStmt)
      | Stmt.whileLoop cond body => Stmt.whileLoop cond (recStmt body)
      | Stmt.doWhile body cond => Stmt.doWhile (recStmt body) cond
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map recStmt) cond post (recStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch expr (clauses.map recClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns expr returns (recStmt success)
            (clauses.map recClause)
      | Stmt.unchecked body => Stmt.unchecked (recStmt body)
      | other => other

def CatchClause.qualifyCollidingEventErrorsFuel :
    Nat -> List Name -> List Name -> CatchClause -> CatchClause
  | 0, _, _, clause => clause
  | fuel + 1, collidingEvents, collidingErrors, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.qualifyCollidingEventErrorsFuel fuel collidingEvents
              collidingErrors body)

end

def Stmt.qualifyCollidingEventErrors
    (collidingEvents collidingErrors : List Name) (stmt : Stmt) : Stmt :=
  Stmt.qualifyCollidingEventErrorsFuel defaultResolveInterfaceIdsFuel
    collidingEvents collidingErrors stmt

def FunctionDecl.qualifyCollidingEventErrors
    (collidingEvents collidingErrors : List Name) (decl : FunctionDecl) :
    FunctionDecl :=
  { decl with
    body :=
      decl.body.map
        (Stmt.qualifyCollidingEventErrors collidingEvents collidingErrors) }

def ContractItem.qualifyCollidingEventErrors
    (collidingEvents collidingErrors : List Name) :
    ContractItem -> ContractItem
  | ContractItem.function decl =>
      ContractItem.function
        (FunctionDecl.qualifyCollidingEventErrors collidingEvents collidingErrors
          decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl
        { decl with
          body :=
            decl.body.map
              (Stmt.qualifyCollidingEventErrors collidingEvents
                collidingErrors) }
  | other => other

def ContractDecl.qualifyCollidingEventErrors
    (collidingEvents collidingErrors : List Name) (decl : ContractDecl) :
    ContractDecl :=
  { decl with
    items :=
      decl.items.map
        (ContractItem.qualifyCollidingEventErrors collidingEvents
          collidingErrors) }

def modifierArgTempName (index : Nat) : Name :=
  "_sol_mod_arg" ++ reprStr index

def modifierParamRuntimeName (index : Nat) : Name :=
  "_sol_mod_param" ++ reprStr index

abbrev NameAliasEnv := List (Name × Name)

def NameAliasEnv.lookup? : NameAliasEnv -> Name -> Option Name
  | [], _ => none
  | (source, target) :: rest, name =>
      if source == name then
        some target
      else
        NameAliasEnv.lookup? rest name

def NameAliasEnv.resolve (env : NameAliasEnv) (name : Name) : Name :=
  (NameAliasEnv.lookup? env name).getD name

def NameAliasEnv.remove (env : NameAliasEnv) (name : Name) : NameAliasEnv :=
  env.filter (fun binding => binding.fst != name)

def VarBinding.removeNameAlias (env : NameAliasEnv)
    (binding : VarBinding) : NameAliasEnv :=
  match binding.name with
  | some name => NameAliasEnv.remove env name
  | none => env

def VarBindings.removeNameAliases :
    NameAliasEnv -> List VarBinding -> NameAliasEnv
  | env, [] => env
  | env, binding :: rest =>
      VarBindings.removeNameAliases
        (VarBinding.removeNameAlias env binding) rest

def Parameter.removeNameAlias (env : NameAliasEnv)
    (param : Parameter) : NameAliasEnv :=
  match param.name with
  | some name => NameAliasEnv.remove env name
  | none => env

def Parameters.removeNameAliases :
    NameAliasEnv -> List Parameter -> NameAliasEnv
  | env, [] => env
  | env, param :: rest =>
      Parameters.removeNameAliases
        (Parameter.removeNameAlias env param) rest

mutual

def Expr.renameIdentsFuel : Nat -> NameAliasEnv -> Expr -> Expr
  | 0, _, expr => expr
  | _ + 1, _, Expr.literal literal => Expr.literal literal
  | _ + 1, env, Expr.ident name => Expr.ident (NameAliasEnv.resolve env name)
  | _ + 1, _, Expr.typeName ty => Expr.typeName ty
  | fuel + 1, env, Expr.member base member =>
      Expr.member (Expr.renameIdentsFuel fuel env base) member
  | fuel + 1, env, Expr.index base index =>
      Expr.index
        (Expr.renameIdentsFuel fuel env base)
        (Expr.renameIdentsFuel fuel env index)
  | fuel + 1, env, Expr.slice base start stop =>
      Expr.slice
        (Expr.renameIdentsFuel fuel env base)
        (start.map (Expr.renameIdentsFuel fuel env))
        (stop.map (Expr.renameIdentsFuel fuel env))
  | fuel + 1, env, Expr.call fn args =>
      Expr.call
        (Expr.renameIdentsFuel fuel env fn)
        (args.map (Arg.renameIdentsFuel fuel env))
  | fuel + 1, env, Expr.callWithOptions fn options args =>
      Expr.callWithOptions
        (Expr.renameIdentsFuel fuel env fn)
        (options.map (CallOption.renameIdentsFuel fuel env))
        (args.map (Arg.renameIdentsFuel fuel env))
  | fuel + 1, env, Expr.newExpr ty args =>
      Expr.newExpr ty (args.map (Arg.renameIdentsFuel fuel env))
  | fuel + 1, env, Expr.tuple items =>
      Expr.tuple (items.map (TupleItem.renameIdentsFuel fuel env))
  | fuel + 1, env, Expr.array exprs =>
      Expr.array (exprs.map (Expr.renameIdentsFuel fuel env))
  | fuel + 1, env, Expr.enumFromUInt maxValue inner =>
      Expr.enumFromUInt maxValue (Expr.renameIdentsFuel fuel env inner)
  | fuel + 1, env, Expr.unary op inner =>
      Expr.unary op (Expr.renameIdentsFuel fuel env inner)
  | fuel + 1, env, Expr.binary op lhs rhs =>
      Expr.binary op
        (Expr.renameIdentsFuel fuel env lhs)
        (Expr.renameIdentsFuel fuel env rhs)
  | fuel + 1, env, Expr.ternary cond thenExpr elseExpr =>
      Expr.ternary
        (Expr.renameIdentsFuel fuel env cond)
        (Expr.renameIdentsFuel fuel env thenExpr)
        (Expr.renameIdentsFuel fuel env elseExpr)
  | fuel + 1, env, Expr.assign lhs op rhs =>
      Expr.assign
        (Expr.renameIdentsFuel fuel env lhs)
        op
        (Expr.renameIdentsFuel fuel env rhs)
  | fuel + 1, env, Expr.payableConversion inner =>
      Expr.payableConversion (Expr.renameIdentsFuel fuel env inner)
termination_by fuel _ _ => fuel

def Arg.renameIdentsFuel : Nat -> NameAliasEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, env, Arg.positional expr =>
      Arg.positional (Expr.renameIdentsFuel fuel env expr)
  | fuel + 1, env, Arg.named name expr =>
      Arg.named name (Expr.renameIdentsFuel fuel env expr)
termination_by fuel _ _ => fuel

def CallOption.renameIdentsFuel : Nat -> NameAliasEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, env, CallOption.named name expr =>
      CallOption.named name (Expr.renameIdentsFuel fuel env expr)
termination_by fuel _ _ => fuel

def TupleItem.renameIdentsFuel : Nat -> NameAliasEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | _ + 1, _, TupleItem.hole => TupleItem.hole
  | fuel + 1, env, TupleItem.value expr =>
      TupleItem.value (Expr.renameIdentsFuel fuel env expr)
termination_by fuel _ _ => fuel

def Stmt.renameIdentsFuel : Nat -> NameAliasEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | _ + 1, _, Stmt.empty => Stmt.empty
  | fuel + 1, env, Stmt.block body =>
      Stmt.block (Stmt.renameIdentSeqFuel fuel env body).fst
  | fuel + 1, env, Stmt.varDecl bindings init =>
      Stmt.varDecl bindings (init.map (Expr.renameIdentsFuel fuel env))
  | fuel + 1, env, Stmt.expr expr =>
      Stmt.expr (Expr.renameIdentsFuel fuel env expr)
  | fuel + 1, env, Stmt.ifElse cond thenBranch elseBranch =>
      Stmt.ifElse
        (Expr.renameIdentsFuel fuel env cond)
        (Stmt.renameIdentsFuel fuel env thenBranch)
        (elseBranch.map (Stmt.renameIdentsFuel fuel env))
  | fuel + 1, env, Stmt.whileLoop cond body =>
      Stmt.whileLoop
        (Expr.renameIdentsFuel fuel env cond)
        (Stmt.renameIdentsFuel fuel env body)
  | fuel + 1, env, Stmt.doWhile body cond =>
      Stmt.doWhile
        (Stmt.renameIdentsFuel fuel env body)
        (Expr.renameIdentsFuel fuel env cond)
  | fuel + 1, env, Stmt.forLoop init cond post body =>
      Stmt.forLoop
        (init.map (Stmt.renameIdentsFuel fuel env))
        (cond.map (Expr.renameIdentsFuel fuel env))
        (post.map (Expr.renameIdentsFuel fuel env))
        (Stmt.renameIdentsFuel fuel env body)
  | fuel + 1, env, Stmt.tryCatch expr clauses =>
      Stmt.tryCatch
        (Expr.renameIdentsFuel fuel env expr)
        (clauses.map (CatchClause.renameIdentsFuel fuel env))
  | fuel + 1, env, Stmt.tryCatchReturns expr returns success clauses =>
      let successEnv := Parameters.removeNameAliases env returns
      Stmt.tryCatchReturns
        (Expr.renameIdentsFuel fuel env expr)
        returns
        (Stmt.renameIdentsFuel fuel successEnv success)
        (clauses.map (CatchClause.renameIdentsFuel fuel env))
  | fuel + 1, env, Stmt.emitEvent expr =>
      Stmt.emitEvent (Expr.renameIdentsFuel fuel env expr)
  | fuel + 1, env, Stmt.revertCall expr =>
      Stmt.revertCall (Expr.renameIdentsFuel fuel env expr)
  | fuel + 1, env, Stmt.returnValues expr? =>
      Stmt.returnValues (expr?.map (Expr.renameIdentsFuel fuel env))
  | _ + 1, _, Stmt.break => Stmt.break
  | _ + 1, _, Stmt.continue => Stmt.continue
  | fuel + 1, env, Stmt.unchecked body =>
      Stmt.unchecked (Stmt.renameIdentsFuel fuel env body)
  | _ + 1, _, Stmt.inlineAssembly code => Stmt.inlineAssembly code
  | _ + 1, _, Stmt.modifierPlaceholder => Stmt.modifierPlaceholder
termination_by fuel _ _ => fuel

def CatchClause.renameIdentsFuel :
    Nat -> NameAliasEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, env, CatchClause.clause name params body =>
      let bodyEnv := Parameters.removeNameAliases env params
      CatchClause.clause name params (Stmt.renameIdentsFuel fuel bodyEnv body)
termination_by fuel _ _ => fuel

def Stmt.renameIdentSeqFuel :
    Nat -> NameAliasEnv -> List Stmt -> List Stmt × NameAliasEnv
  | 0, env, stmts => (stmts, env)
  | fuel + 1, env, Stmt.varDecl bindings init :: rest =>
      let head :=
        Stmt.renameIdentsFuel fuel env (Stmt.varDecl bindings init)
      let env' := VarBindings.removeNameAliases env bindings
      let (tail, finalEnv) := Stmt.renameIdentSeqFuel fuel env' rest
      (head :: tail, finalEnv)
  | fuel + 1, env, stmt :: rest =>
      let head := Stmt.renameIdentsFuel fuel env stmt
      let (tail, finalEnv) := Stmt.renameIdentSeqFuel fuel env rest
      (head :: tail, finalEnv)
  | _ + 1, env, [] => ([], env)
termination_by fuel _ _ => fuel

end

def defaultRenameIdentsFuel : Nat := 1024

def Expr.renameIdents (env : NameAliasEnv) (expr : Expr) : Expr :=
  Expr.renameIdentsFuel defaultRenameIdentsFuel env expr

def Arg.renameIdents (env : NameAliasEnv) (arg : Arg) : Arg :=
  Arg.renameIdentsFuel defaultRenameIdentsFuel env arg

def ModifierInvocation.renameIdents (env : NameAliasEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with args := invocation.args.map (Arg.renameIdents env) }

def Stmt.renameIdents (env : NameAliasEnv) (stmt : Stmt) : Stmt :=
  Stmt.renameIdentsFuel defaultRenameIdentsFuel env stmt

/-! ### Internal-function-pointer value uses (boundary-completion arc, stage C)

A function identifier used in VALUE position (not as the callee of a direct
call) is an internal-function-pointer value; solc via-IR assigns such functions
small sequential dispatch IDs (1..n, first-use order; 0 = uninitialized) and
compiles the identifier to the literal ID
(`docs/refs-completion-solc-research.md` §2). The collector enumerates value
uses (first-use order) to build the per-contract numbering; the rewriter
replaces each such identifier with its ID as a number literal, which
`Expr.toCoreAsWithEnv?` then elaborates to the core
`Expr.internalFunction` pointer literal in internal-fn-typed contexts.

Positions: everywhere except the callee slot of `Expr.call`/`callWithOptions`
(a direct call, not a value use). Member-form value uses (`Lib.f`,
`Contract.f`) ARE collected/rewritten (boundary-completion arc, member-form
residue): a contract-member key is the plain member name; a library-member key
is the mangled library-helper name (a library's internal helper is elaborated
under `libraryHelperName`, not its bare name), so both keys are probed against
the numbering candidates.

LEXICAL SCOPE (shadowing soundness fix): solc only WARNS on a param/local/
for-binding shadowing a function name, and resolves the identifier to the
NEAREST declaration — the local always wins in value position. Both the
collector and the rewriter therefore thread the set of locally BOUND names
(function params and named returns, local `varDecl` bindings with C99 block
scoping — in scope from the declaration to the end of its enclosing block —
for-loop init bindings scoping over cond/post/body, and try/catch clause
bindings): a bound identifier is NEVER treated as a function-value reference,
and the same name is a function value again after the shadowing block ends. -/

/-- Mangled name a library internal helper is elaborated under (kept in sync
    with `libraryHelperName`, defined later for the library-call surface). The
    member-form fn-value collector/rewriter need it before that definition. -/
def libraryHelperName (libraryName functionName : Name) : Name :=
  "__library_" ++ libraryName ++ "_" ++ functionName

/-- Both numbering keys a member-form fn-value `Base.member` could resolve to:
    the library-helper mangling (when `Base` is a library) and the plain member
    name (when `Base` is the current/ancestor contract). The candidate filter
    picks whichever actually names an elaborated function. -/
def memberFnValueKeys : Expr -> Name -> List Name
  | Expr.typeName (Ty.user path), member =>
      match path.segments.getLast? with
      | some libraryName => [libraryHelperName libraryName member, member]
      | none => [member]
  | _, _ => []

/-- Names a statement binds for its FOLLOWING siblings (C99 block scoping):
    only a local variable declaration introduces such bindings. -/
def Stmt.localBindingNames : Stmt -> List Name
  | Stmt.varDecl bindings _ => bindings.filterMap (fun b => b.name)
  | _ => []

def Parameters.boundNames (params : List Parameter) : List Name :=
  params.filterMap (fun p => p.name)

/-- Names bound over a function body before any statement runs: the params and
    the named return variables. -/
def FunctionDecl.fnValueScopeBoundNames (fn : FunctionDecl) : List Name :=
  Parameters.boundNames fn.params ++ Parameters.boundNames fn.returns

def Expr.collectInternalFnValueIdentsFuel (candidates bound : List Name) :
    Nat -> Expr -> List Name
  | 0, _ => []
  | fuel + 1, expr =>
      let go := Expr.collectInternalFnValueIdentsFuel candidates bound fuel
      let goArg : Arg -> List Name
        | Arg.positional value => go value
        | Arg.named _ value => go value
      let goOption : CallOption -> List Name
        | CallOption.named _ value => go value
      let goItem : TupleItem -> List Name
        | TupleItem.hole => []
        | TupleItem.value value => go value
      match expr with
      | Expr.ident name =>
          -- A locally BOUND name (param/named return/local/for-binding in
          -- scope) is the LOCAL, never a function-value reference (solc
          -- resolves the nearest declaration; shadowing soundness fix).
          if candidates.contains name && !bound.contains name then [name]
          else []
      | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
          (Arg.positional functionPointer :: rest) =>
          -- `abi.encodeCall(T.f, args)` uses the type-qualified external
          -- declaration to derive the selector and parameter types. `T.f` is
          -- not an internal-function value in this position.
          (match functionPointer with
          | Expr.member (Expr.typeName _) _ => []
          | _ => go functionPointer) ++ concatMapList goArg rest
      | Expr.call fn args =>
          (match fn with
            | Expr.ident _ => []
            -- A member-form call `Lib.f(..)` / `Contract.f(..)` is a direct
            -- call, NOT a value use of `f`.
            | Expr.member (Expr.typeName _) _ => []
            | _ => go fn) ++ concatMapList goArg args
      | Expr.callWithOptions fn options args =>
          (match fn with
            | Expr.ident _ => []
            | Expr.member (Expr.typeName _) _ => []
            | _ => go fn) ++
            concatMapList goOption options ++ concatMapList goArg args
      -- Member-form internal-function VALUE (`Lib.f` / `Contract.f`): the same
      -- dispatch numbering as a bare identifier, keyed by the library-helper
      -- name (library base) or the plain member name (contract base).
      | Expr.member (Expr.typeName tyName) member =>
          match (memberFnValueKeys (Expr.typeName tyName) member).find?
              candidates.contains with
          | some key => [key]
          | none => []
      | Expr.member base _ => go base
      | Expr.index base index => go base ++ go index
      | Expr.slice base start stop =>
          go base ++
            (match start with | some e => go e | none => []) ++
            (match stop with | some e => go e | none => [])
      | Expr.newExpr _ args => concatMapList goArg args
      | Expr.tuple items => concatMapList goItem items
      | Expr.array values => concatMapList go values
      | Expr.enumFromUInt _ value => go value
      | Expr.unary _ value => go value
      | Expr.binary _ lhs rhs => go lhs ++ go rhs
      | Expr.ternary cond thenExpr elseExpr =>
          go cond ++ go thenExpr ++ go elseExpr
      | Expr.assign lhs _ rhs => go lhs ++ go rhs
      | Expr.payableConversion value => go value
      | _ => []

def Stmt.collectInternalFnValueIdentsFuel (candidates bound : List Name) :
    Nat -> Stmt -> List Name
  | 0, _ => []
  | fuel + 1, stmt =>
      let goE := Expr.collectInternalFnValueIdentsFuel candidates bound (fuel + 1)
      let goS := Stmt.collectInternalFnValueIdentsFuel candidates bound fuel
      let goClause : CatchClause -> List Name
        | CatchClause.clause _ params body =>
            Stmt.collectInternalFnValueIdentsFuel candidates
              (bound ++ Parameters.boundNames params) fuel body
      match stmt with
      | Stmt.block stmts =>
          -- C99 block scoping: a varDecl's bindings shadow for the FOLLOWING
          -- statements of this block only.
          (stmts.foldl
            (fun (acc : List Name × List Name) s =>
              (acc.1 ++
                  Stmt.collectInternalFnValueIdentsFuel candidates acc.2 fuel s,
                acc.2 ++ Stmt.localBindingNames s))
            ([], bound)).1
      | Stmt.varDecl _ init =>
          (match init with | some e => goE e | none => [])
      | Stmt.expr e => goE e
      | Stmt.ifElse cond thenBranch elseBranch =>
          goE cond ++ goS thenBranch ++
            (match elseBranch with | some b => goS b | none => [])
      | Stmt.whileLoop cond body => goE cond ++ goS body
      | Stmt.doWhile body cond => goS body ++ goE cond
      | Stmt.forLoop init cond post body =>
          -- The for-init's bindings scope over cond/post/body.
          let boundIn :=
            bound ++
              (match init with
                | some i => Stmt.localBindingNames i
                | none => [])
          let goEIn :=
            Expr.collectInternalFnValueIdentsFuel candidates boundIn (fuel + 1)
          let goSIn :=
            Stmt.collectInternalFnValueIdentsFuel candidates boundIn fuel
          (match init with | some i => goS i | none => []) ++
            (match cond with | some c => goEIn c | none => []) ++
            (match post with | some e => goEIn e | none => []) ++ goSIn body
      | Stmt.tryCatch e clauses => goE e ++ concatMapList goClause clauses
      | Stmt.tryCatchReturns e params success clauses =>
          goE e ++
            Stmt.collectInternalFnValueIdentsFuel candidates
              (bound ++ Parameters.boundNames params) fuel success ++
            concatMapList goClause clauses
      | Stmt.emitEvent e => goE e
      | Stmt.revertCall e => goE e
      | Stmt.returnValues init =>
          (match init with | some e => goE e | none => [])
      | Stmt.unchecked body => goS body
      | _ => []

def Expr.rewriteInternalFnValueIdentsFuel (ids : List (Name × Nat))
    (bound : List Name) :
    Nat -> Expr -> Expr
  | 0, expr => expr
  | fuel + 1, expr =>
      let go := Expr.rewriteInternalFnValueIdentsFuel ids bound fuel
      let goArg : Arg -> Arg
        | Arg.positional value => Arg.positional (go value)
        | Arg.named name value => Arg.named name (go value)
      let goOption : CallOption -> CallOption
        | CallOption.named name value => CallOption.named name (go value)
      let goItem : TupleItem -> TupleItem
        | TupleItem.hole => TupleItem.hole
        | TupleItem.value value => TupleItem.value (go value)
      match expr with
      | Expr.ident name =>
          -- A locally BOUND name is the LOCAL, never a function value; leave
          -- it alone (shadowing soundness fix).
          if bound.contains name then expr
          else
            (match ids.lookup name with
              | some id => Expr.literal (Literal.number (toString id))
              | none => expr)
      | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
          (Arg.positional functionPointer :: rest) =>
          let functionPointer :=
            match functionPointer with
            | Expr.member (Expr.typeName _) _ => functionPointer
            | _ => go functionPointer
          Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
            (Arg.positional functionPointer :: rest.map goArg)
      | Expr.call fn args =>
          Expr.call
            (match fn with
              | Expr.ident _ => fn
              | Expr.member (Expr.typeName _) _ => fn
              | _ => go fn)
            (args.map goArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions
            (match fn with
              | Expr.ident _ => fn
              | Expr.member (Expr.typeName _) _ => fn
              | _ => go fn)
            (options.map goOption) (args.map goArg)
      -- Member-form internal-function VALUE (`Lib.f` / `Contract.f`) in value
      -- position becomes its dispatch-ID literal, under the library-helper name
      -- (library base) or the plain member name (contract base) — the same ID
      -- the numbering assigned.
      | Expr.member (Expr.typeName tyName) member =>
          (match
              (memberFnValueKeys (Expr.typeName tyName) member).findSome?
                (fun k => ids.lookup k) with
            | some id => Expr.literal (Literal.number (toString id))
            | none => Expr.member (Expr.typeName tyName) member)
      | Expr.member base member => Expr.member (go base) member
      | Expr.index base index => Expr.index (go base) (go index)
      | Expr.slice base start stop =>
          Expr.slice (go base) (start.map go) (stop.map go)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map goArg)
      | Expr.tuple items => Expr.tuple (items.map goItem)
      | Expr.array values => Expr.array (values.map go)
      | Expr.enumFromUInt w value => Expr.enumFromUInt w (go value)
      | Expr.unary op value => Expr.unary op (go value)
      | Expr.binary op lhs rhs => Expr.binary op (go lhs) (go rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (go cond) (go thenExpr) (go elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (go lhs) op (go rhs)
      | Expr.payableConversion value => Expr.payableConversion (go value)
      | _ => expr

def Stmt.rewriteInternalFnValueIdentsFuel (ids : List (Name × Nat))
    (bound : List Name) :
    Nat -> Stmt -> Stmt
  | 0, stmt => stmt
  | fuel + 1, stmt =>
      let goE := Expr.rewriteInternalFnValueIdentsFuel ids bound (fuel + 1)
      let goS := Stmt.rewriteInternalFnValueIdentsFuel ids bound fuel
      let goClause : CatchClause -> CatchClause
        | CatchClause.clause name params body =>
            CatchClause.clause name params
              (Stmt.rewriteInternalFnValueIdentsFuel ids
                (bound ++ Parameters.boundNames params) fuel body)
      match stmt with
      | Stmt.block stmts =>
          -- C99 block scoping, mirroring the collector: a varDecl's bindings
          -- shadow for the FOLLOWING statements of this block only.
          Stmt.block
            ((stmts.foldl
              (fun (acc : List Stmt × List Name) s =>
                (acc.1 ++
                    [Stmt.rewriteInternalFnValueIdentsFuel ids acc.2 fuel s],
                  acc.2 ++ Stmt.localBindingNames s))
              ([], bound)).1)
      | Stmt.varDecl bindings init => Stmt.varDecl bindings (init.map goE)
      | Stmt.expr e => Stmt.expr (goE e)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (goE cond) (goS thenBranch) (elseBranch.map goS)
      | Stmt.whileLoop cond body => Stmt.whileLoop (goE cond) (goS body)
      | Stmt.doWhile body cond => Stmt.doWhile (goS body) (goE cond)
      | Stmt.forLoop init cond post body =>
          -- The for-init's bindings scope over cond/post/body.
          let boundIn :=
            bound ++
              (match init with
                | some i => Stmt.localBindingNames i
                | none => [])
          let goEIn := Expr.rewriteInternalFnValueIdentsFuel ids boundIn (fuel + 1)
          let goSIn := Stmt.rewriteInternalFnValueIdentsFuel ids boundIn fuel
          Stmt.forLoop (init.map goS) (cond.map goEIn) (post.map goEIn)
            (goSIn body)
      | Stmt.tryCatch e clauses =>
          Stmt.tryCatch (goE e) (clauses.map goClause)
      | Stmt.tryCatchReturns e params success clauses =>
          Stmt.tryCatchReturns (goE e) params
            (Stmt.rewriteInternalFnValueIdentsFuel ids
              (bound ++ Parameters.boundNames params) fuel success)
            (clauses.map goClause)
      | Stmt.emitEvent e => Stmt.emitEvent (goE e)
      | Stmt.revertCall e => Stmt.revertCall (goE e)
      | Stmt.returnValues init => Stmt.returnValues (init.map goE)
      | Stmt.unchecked body => Stmt.unchecked (goS body)
      | _ => stmt

def Stmt.rewriteInternalFnValueIdents (ids : List (Name × Nat))
    (bound : List Name) (stmt : Stmt) : Stmt :=
  if ids.isEmpty then stmt
  else
    Stmt.rewriteInternalFnValueIdentsFuel ids bound
      defaultInlineConstantsFuel stmt

/-- Distribute a call whose callee is a ternary that SELECTS between two internal
    functions (`(cond ? a : b)(args)`) over the two branches
    (`cond ? a(args) : b(args)`). solc evaluates the callee first (which
    evaluates `cond` and selects a function pointer), then the arguments, then
    calls the selected function — so pushing the call into each branch preserves
    the observable order: `cond` runs once, `args` run once in the taken branch,
    the selected function runs once. Applied BEFORE the fn-value dispatch-ID
    rewrite so the branch functions become ordinary NAME-resolved direct calls
    (`Expr.call (Expr.ident a) args`), which the internal-call lowering already
    handles — the alternative (a call THROUGH the ternary as a function pointer)
    cannot recover the pointer type once the identifiers become dispatch-ID
    literals. Non-ternary callees (including `arr[i](x)` pointer callees) are
    left untouched. -/
def Expr.distributeTernaryCallCalleeFuel : Nat -> Expr -> Expr
  | 0, expr => expr
  | fuel + 1, expr =>
      let go := Expr.distributeTernaryCallCalleeFuel fuel
      let goArg : Arg -> Arg
        | Arg.positional value => Arg.positional (go value)
        | Arg.named name value => Arg.named name (go value)
      let goOption : CallOption -> CallOption
        | CallOption.named name value => CallOption.named name (go value)
      let goItem : TupleItem -> TupleItem
        | TupleItem.hole => TupleItem.hole
        | TupleItem.value value => TupleItem.value (go value)
      match expr with
      | Expr.call fn args =>
          let fn' := go fn
          let args' := args.map goArg
          (match fn' with
            | Expr.ternary cond thenExpr elseExpr =>
                Expr.ternary cond
                  (go (Expr.call thenExpr args'))
                  (go (Expr.call elseExpr args'))
            | _ => Expr.call fn' args')
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (go fn) (options.map goOption) (args.map goArg)
      | Expr.member base member => Expr.member (go base) member
      | Expr.index base index => Expr.index (go base) (go index)
      | Expr.slice base start stop =>
          Expr.slice (go base) (start.map go) (stop.map go)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map goArg)
      | Expr.tuple items => Expr.tuple (items.map goItem)
      | Expr.array values => Expr.array (values.map go)
      | Expr.enumFromUInt w value => Expr.enumFromUInt w (go value)
      | Expr.unary op value => Expr.unary op (go value)
      | Expr.binary op lhs rhs => Expr.binary op (go lhs) (go rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (go cond) (go thenExpr) (go elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (go lhs) op (go rhs)
      | Expr.payableConversion value => Expr.payableConversion (go value)
      | _ => expr

def Stmt.distributeTernaryCallCalleeFuel : Nat -> Stmt -> Stmt
  | 0, stmt => stmt
  | fuel + 1, stmt =>
      let goE := Expr.distributeTernaryCallCalleeFuel defaultInlineConstantsFuel
      let goS := Stmt.distributeTernaryCallCalleeFuel fuel
      let goClause : CatchClause -> CatchClause
        | CatchClause.clause name params body =>
            CatchClause.clause name params (goS body)
      match stmt with
      | Stmt.block stmts => Stmt.block (stmts.map goS)
      | Stmt.varDecl bindings init => Stmt.varDecl bindings (init.map goE)
      | Stmt.expr e => Stmt.expr (goE e)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (goE cond) (goS thenBranch) (elseBranch.map goS)
      | Stmt.whileLoop cond body => Stmt.whileLoop (goE cond) (goS body)
      | Stmt.doWhile body cond => Stmt.doWhile (goS body) (goE cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map goS) (cond.map goE) (post.map goE) (goS body)
      | Stmt.tryCatch e clauses =>
          Stmt.tryCatch (goE e) (clauses.map goClause)
      | Stmt.tryCatchReturns e params success clauses =>
          Stmt.tryCatchReturns (goE e) params (goS success)
            (clauses.map goClause)
      | Stmt.emitEvent e => Stmt.emitEvent (goE e)
      | Stmt.revertCall e => Stmt.revertCall (goE e)
      | Stmt.returnValues init => Stmt.returnValues (init.map goE)
      | Stmt.unchecked body => Stmt.unchecked (goS body)
      | _ => stmt

def Stmt.distributeTernaryCallCallee (stmt : Stmt) : Stmt :=
  Stmt.distributeTernaryCallCalleeFuel defaultInlineConstantsFuel stmt

/-- First-use-order deduplication. -/
def Names.dedupPreservingOrder (names : List Name) : List Name :=
  (names.foldl
    (fun (acc : List Name × List Name) name =>
      let (kept, seen) := acc
      if seen.contains name then acc else (kept ++ [name], name :: seen))
    ([], [])).1

/-- Per-contract internal-dispatch numbering (stage C): scan the given function
    bodies (declaration order) for function identifiers used as VALUES and
    assign IDs 1..n in first-use order, mirroring solc via-IR's internal
    dispatch. -/
def FunctionDecls.internalFnValueNumbering
    (candidates : List Name) (fns : List FunctionDecl) : List (Name × Nat) :=
  let uses :=
    concatMapList
      (fun (fn : FunctionDecl) =>
        match fn.body with
        | some body =>
            Stmt.collectInternalFnValueIdentsFuel candidates
              (FunctionDecl.fnValueScopeBoundNames fn)
              defaultInlineConstantsFuel body
        | none => [])
      fns
  let ordered := Names.dedupPreservingOrder uses
  (ordered.zipIdx.map (fun p => (p.fst, p.snd + 1)))

/-- Internal-dispatch numbering including value uses in MODIFIER and CONSTRUCTOR
    bodies (boundary-completion arc, ctor/modifier residue). Ordinary-function
    value uses are numbered FIRST (identical to `internalFnValueNumbering`), then
    modifier-body uses, then constructor-body uses are appended; the shared
    first-use dedup keeps the ordinary-only IDs stable, so lanes without
    ctor/modifier fn-values are unaffected. Both the runtime-table elaboration
    (`toCoreFromOrders?`) and the constructor elaboration
    (`constructorFunctionFromOrders?`) call this with identical arguments so the
    IDs stamped on the dispatch table agree with the IDs the constructor writes
    into storage. -/
def FunctionDecls.internalFnValueNumberingFull
    (candidates : List Name) (fns : List FunctionDecl)
    (modifiers : List SourceModifierDecl)
    (constructors : List FunctionDecl)
    (stateInitializers : List Expr := []) : List (Name × Nat) :=
  let collectBody (bound : List Name) : Stmt -> List Name :=
    Stmt.collectInternalFnValueIdentsFuel candidates bound
      defaultInlineConstantsFuel
  let fnUses :=
    concatMapList
      (fun (fn : FunctionDecl) =>
        match fn.body with
        | some body =>
            collectBody (FunctionDecl.fnValueScopeBoundNames fn) body
        | none => [])
      fns
  let modifierUses :=
    concatMapList
      (fun (m : SourceModifierDecl) =>
        match m.body with
        | some body => collectBody (Parameters.boundNames m.params) body
        | none => [])
      modifiers
  let constructorUses :=
    concatMapList
      (fun (ctor : FunctionDecl) =>
        match ctor.body with
        | some body =>
            collectBody (FunctionDecl.fnValueScopeBoundNames ctor) body
        | none => [])
      constructors
  let initializerUses :=
    concatMapList
      (Expr.collectInternalFnValueIdentsFuel candidates []
        defaultInlineConstantsFuel)
      stateInitializers
  let ordered :=
    Names.dedupPreservingOrder
      (fnUses ++ modifierUses ++ constructorUses ++ initializerUses)
  (ordered.zipIdx.map (fun p => (p.fst, p.snd + 1)))

def Parameter.runtimeName (fallbackPrefix : String) (index : Nat) : Name :=
  fallbackPrefix ++ toString index

def Parameter.withRuntimeName (fallbackPrefix : String) (index : Nat)
    (param : Parameter) : Parameter :=
  { param with name := some (Parameter.runtimeName fallbackPrefix index) }

def Parameters.withRuntimeNames (fallbackPrefix : String)
    (params : List Parameter) : List Parameter :=
  mapIdx (Parameter.withRuntimeName fallbackPrefix) 0 params

def ModifierDecl.paramAliasEnv (decl : SourceModifierDecl) : NameAliasEnv :=
  mapIdx
    (fun index param =>
      match param.name with
      | some name => some (name, modifierParamRuntimeName index)
      | none => none)
    0 decl.params |>.filterMap id

def ModifierDecl.aliasedParams (decl : SourceModifierDecl) : List Parameter :=
  mapIdx
    (fun index param =>
      { param with name := some (modifierParamRuntimeName index) })
    0 decl.params

def ModifierDecl.aliasParamsInBody
    (decl : SourceModifierDecl) (body : Stmt) : Stmt :=
  Stmt.renameIdents (ModifierDecl.paramAliasEnv decl) body

def modifierParamBindingsFrom? :
    Nat -> List Parameter -> List Expr -> Option (List Stmt)
  | _, [], [] => some []
  | index, param :: params, arg :: args => do
      let rest ← modifierParamBindingsFrom? (index + 1) params args
      let tempName := modifierArgTempName index
      some
        ( Stmt.varDecl
            [{ name := some tempName
               ty := some param.ty
               location := param.location }]
            (some arg)
          :: Stmt.varDecl
            [{ name := some (modifierParamRuntimeName index)
               ty := some param.ty
               location := param.location }]
            (some (Expr.ident tempName))
          :: rest)
  | _, _, _ => none

def modifierParamBindingsWithArgs? (decl : SourceModifierDecl)
    (args : List Arg) : Option (List Stmt) := do
  let orderedArgs ← Args.toExprsForParams? decl.params args
  modifierParamBindingsFrom? 0 decl.params orderedArgs

def modifierApply? (decl : SourceModifierDecl)
    (invocation : SourceModifierInvocation) (inner : Stmt) : Option Stmt := do
  let body ← decl.body
  let body := ModifierDecl.aliasParamsInBody decl body
  let prefixStmts ← modifierParamBindingsWithArgs? decl invocation.args
  some
    (Stmt.block
      (prefixStmts ++ [Stmt.replaceTopLevelModifierPlaceholder inner body]))

def modifierFindByName? (modifiers : List SourceModifierDecl)
    (name : Name) : Option SourceModifierDecl :=
  modifiers.find? (fun modifier => modifier.name == name)

/-- Resolve a modifier invocation TARGET path against the available modifiers.

An UNQUALIFIED target (`m`, a single-segment path) resolves VIRTUALLY: the
first name match over the most-derived-first `modifiers` list, i.e. the
most-derived override (unchanged behavior).

A QUALIFIED target (`Base.m`, multi-segment) resolves STATICALLY (solc
`VirtualLookup::Static`): the qualifier segment names the base contract, and we
bind to THAT contract's own modifier named by the last segment. This requires
the modifiers to carry `declaringContract` (see `directModifiersStamped`); if
no stamped match exists (unstamped list, or the qualifier is not a contract in
the linearization) we fall back to the virtual name-first lookup so no path
regresses. -/
def modifierResolve? (modifiers : List SourceModifierDecl)
    (target : Path) : Option SourceModifierDecl := do
  let name ← pathLast? target
  match target.segments with
  | _ :: _ :: _ =>
      -- Qualified `...Qualifier.name`: the contract qualifier is the segment
      -- immediately before the modifier name (last segment of the path init).
      let qualifier ← target.segments.dropLast.reverse.head?
      match modifiers.find?
          (fun modifier =>
            modifier.declaringContract == some qualifier &&
              modifier.name == name) with
      | some modifier => some modifier
      | none => modifierFindByName? modifiers name
  | _ => modifierFindByName? modifiers name

inductive ModifierApplicationStatus where
  | applied
  | badTarget
  | missingModifier
  | missingBody
  | badArguments
  | coreExpansionFailed
  deriving Repr, BEq

def FunctionDecl.coreName? (decl : FunctionDecl) : Option Name :=
  match decl.kind with
  | FunctionKind.function => decl.name
  | FunctionKind.receive => some "__receive"
  | FunctionKind.fallback => some "__fallback"
  | FunctionKind.constructor => none

def FunctionDecl.isPayable (decl : FunctionDecl) : Bool :=
  match decl.mutability with
  | StateMutability.payable => true
  | _ => false

def FunctionDecl.isExternallyNamedFunction (decl : FunctionDecl) : Bool :=
  match decl.kind with
  | FunctionKind.function => true
  | _ => false

def FunctionDecl.isCoreEntrypoint (decl : FunctionDecl) : Bool :=
  match decl.visibility with
  | some Visibility.internal_
  | some Visibility.private_ => false
  | _ => true

mutual

def Ty.matchesShape : Ty -> Ty -> Bool
  | Ty.bool, Ty.bool => true
  | Ty.address _, Ty.address _ => true
  | Ty.uint lhs, Ty.uint rhs =>
      (lhs == rhs) || (lhs == 0 && rhs == 256) || (lhs == 256 && rhs == 0)
  | Ty.int lhs, Ty.int rhs =>
      (lhs == rhs) || (lhs == 0 && rhs == 256) || (lhs == 256 && rhs == 0)
  | Ty.bytesN lhs, Ty.bytesN rhs => lhs == rhs
  | Ty.fixedBytes lhs, Ty.fixedBytes rhs => lhs == rhs
  -- BUG#6: enum shape-matching is NOMINAL — canonical path AND member bound.
  | Ty.enum lhsPath lhs, Ty.enum rhsPath rhs =>
      lhsPath == rhsPath && lhs == rhs
  | Ty.bytes, Ty.bytes => true
  | Ty.string, Ty.string => true
  | Ty.array lhsTy lhsSize?, Ty.array rhsTy rhsSize? =>
      lhsSize? == rhsSize? && Ty.matchesShape lhsTy rhsTy
  | Ty.mapping lhsKey lhsValue, Ty.mapping rhsKey rhsValue =>
      Ty.matchesShape lhsKey rhsKey && Ty.matchesShape lhsValue rhsValue
  | Ty.tuple lhs, Ty.tuple rhs => Ty.listMatchesShape lhs rhs
  | Ty.struct lhsPath lhs, Ty.struct rhsPath rhs =>
      Path.matchesNominal lhsPath rhsPath && Ty.listMatchesShape lhs rhs
  | Ty.tuple lhs, Ty.struct _ rhs => Ty.listMatchesShape lhs rhs
  | Ty.struct _ lhs, Ty.tuple rhs => Ty.listMatchesShape lhs rhs
  | Ty.user lhs, Ty.user rhs => Path.matchesNominal lhs rhs
  | Ty.user lhs, Ty.struct rhs _ => Path.matchesNominal lhs rhs
  | Ty.struct lhs _, Ty.user rhs => Path.matchesNominal lhs rhs
  | _, _ => false

def Ty.listMatchesShape : List Ty -> List Ty -> Bool
  | [], [] => true
  | lhs :: lhsRest, rhs :: rhsRest =>
      Ty.matchesShape lhs rhs && Ty.listMatchesShape lhsRest rhsRest
  | _, _ => false

end

def Parameter.matchesArg? (env : TypeEnv) (param : Parameter)
    (arg : Expr) : Option Bool := do
  let argTy ←
    match arg with
    -- Overload selection: an ENUM-typed argument (a member literal `E.B` or an
    -- explicit conversion `E(x)`, both lowered to `enumFromUInt` by
    -- `resolveEnums`) selects candidates as its ENUM type, exactly as solc
    -- binds it. `abiTy?` reflects `enumFromUInt` as its underlying `uint 8`
    -- (the ABI/packing width, #178); letting that leak into candidate
    -- selection bound `f(uint8)` over `f(E)` — a wrong-callee soundness bug.
    | Expr.enumFromUInt maxValue _ =>
        -- MERGE RECONCILIATION (call-rewrite × BUG#6): `Ty.enum` is now
        -- nominal (`Path -> Nat -> Ty`), but the lowered enum literal carries
        -- only its member bound — the declaring path is unrecoverable after
        -- `resolveEnums`. Selection therefore matches PATH-BLIND by borrowing
        -- the candidate param's own path: the member bound alone decides,
        -- which is exactly the pre-BUG#6 selection semantics this fix shipped
        -- with. A non-enum param gets a nominal-empty path and mismatches on
        -- the constructor as before.
        match param.ty with
        | Ty.enum paramPath _ => some (Ty.enum paramPath maxValue)
        | _ => some (Ty.enum ⟨[]⟩ maxValue)
    | _ => Expr.abiTyWithEnv? env arg
  some (Ty.matchesShape argTy param.ty)

def Parameter.matchesArgAllowingInternalFunctionName?
    (env : TypeEnv) (param : Parameter) (arg : Expr) : Option Bool :=
  match param.ty, arg with
  | Ty.functionWithLocations _ _ _ _ _ Visibility.internal_, Expr.ident _ =>
      some true
  | _, _ => Parameter.matchesArg? env param arg

/-- Reference-vs-value classification for the arity-fallback wrong-callee
    guard: `some true` for reference/aggregate-shaped types, `some false` for
    value-shaped types, `none` when undecidable. -/
def Ty.arityFallbackReferenceClass? : Ty -> Option Bool
  | Ty.array _ _ => some true
  | Ty.struct _ _ => some true
  | Ty.tuple _ => some true
  | Ty.mapping _ _ => some true
  | Ty.bytes => some true
  | Ty.string => some true
  | Ty.uint _ => some false
  | Ty.int _ => some false
  | Ty.bool => some false
  | Ty.address _ => some false
  | Ty.bytesN _ => some false
  | Ty.fixedBytes _ => some false
  | Ty.enum _ _ => some false
  | _ => none

/-- Arity-fallback TYPE SAFETY: a candidate is EXCLUDED only when an
    argument's type is KNOWN and DEFINITELY mismatches a resolved parameter
    type. Untypeable arguments (the gate returns `none`) and unresolved
    `Ty.user` parameters cannot be disproven, so they stay compatible — this
    keeps the decf368 coverage win (shapes the gate does not model still
    rewrite) while stopping the fallback from binding a same-arity overload
    whose parameter types are incompatible with the arguments (wrong-callee
    soundness bug). -/
def Parameter.arityFallbackCompatible (env : TypeEnv)
    (param : Parameter) (arg : Expr) : Bool :=
  match param.ty with
  | Ty.user _ => true
  | Ty.functionWithLocations _ _ _ _ _ _ =>
      -- Function-typed params are UNDECIDABLE here: a function-pointer
      -- argument takes many lowered shapes (a bare name ident, a
      -- dispatch-ID number after `rewriteInternalFnValueIdents`, a member
      -- path), which the expression typer reports as scalars — a "definite
      -- mismatch" against them is untrustworthy (internal-fn-pointers /
      -- refs-residue-fn-values lanes).
      true
  | _ =>
      match arg with
      | Expr.literal _ =>
          -- Literals have conversion latitude the shape gate does not model
          -- (number literals fit any wide-enough numeric type, string/hex
          -- literals fit bytesN); never disprove a candidate on a literal.
          true
      | _ =>
          -- CROSS-CLASS disproof ONLY: the sole implication solid enough to
          -- exclude a candidate is reference/aggregate (array, struct, tuple,
          -- mapping, bytes, string) vs value (numeric, bool, address, bytesN,
          -- enum) — solc has NO implicit conversion across that divide for a
          -- non-literal argument. WITHIN a class the reported type is not a
          -- disproof: widening (`uint8 -> uint256`), constant folding
          -- (`g(2 - 2)` converts to `bytes32` because the fold is zero), and
          -- enum borrowing all defeat a naive shape comparison.
          match Ty.arityFallbackReferenceClass? param.ty,
              (Expr.abiTyWithEnv? env arg).bind
                Ty.arityFallbackReferenceClass? with
          | some paramIsRef, some argIsRef => paramIsRef == argIsRef
          | _, _ => true

def Parameters.arityFallbackCompatible (env : TypeEnv) :
    List Parameter -> List Expr -> Bool
  | [], [] => true
  | param :: params, arg :: args =>
      Parameter.arityFallbackCompatible env param arg &&
        Parameters.arityFallbackCompatible env params args
  | _, _ => false

def Parameters.matchArgsWithEnv? (env : TypeEnv) :
    List Parameter -> List Expr -> Option Bool
  | [], [] => some true
  | param :: params, arg :: args => do
      let head ← Parameter.matchesArg? env param arg
      let tail ← Parameters.matchArgsWithEnv? env params args
      some (head && tail)
  | _, _ => some false

def Parameters.matchArgsAllowingInternalFunctionNamesWithEnv?
    (env : TypeEnv) :
    List Parameter -> List Expr -> Option Bool
  | [], [] => some true
  | param :: params, arg :: args => do
      let head ←
        Parameter.matchesArgAllowingInternalFunctionName? env param arg
      let tail ←
        Parameters.matchArgsAllowingInternalFunctionNamesWithEnv?
          env params args
      some (head && tail)
  | _, _ => some false

def FunctionDecl.findInternalCallee? (functions : List FunctionDecl)
    (env : TypeEnv) (name : Name) (args : List Expr) :
    Option FunctionDecl :=
  let candidates :=
    functions.filter (fun fn =>
      match fn.name with
      | some fnName =>
          fnName == name && fn.params.length == args.length &&
            FunctionDecl.isExternallyNamedFunction fn
      | none => false)
  match candidates.find? (fun fn =>
      match Parameters.matchArgsAllowingInternalFunctionNamesWithEnv?
          env fn.params args with
      | some true => true
      | _ => false) with
  | some fn => some fn
  | none =>
      -- Arity fallback: exclude candidates whose KNOWN arg types definitely
      -- mismatch (`Parameters.arityFallbackCompatible`) — same wrong-callee
      -- guard as the library direct-call fallback; accept-when-unknown is
      -- preserved.
      (candidates.filter (fun fn =>
        Parameters.arityFallbackCompatible env fn.params args)).head?

def FunctionDecl.orderedArgs? (decl : FunctionDecl)
    (args : List Arg) : Option (List Expr) :=
  Args.toExprsForParams? decl.params args

def FunctionDecl.findInternalCalleeWithArgs?
    (functions : List FunctionDecl) (env : TypeEnv)
    (name : Name) (args : List Arg) :
    Option (FunctionDecl × List Expr) :=
  let candidates :=
    functions.filter (fun fn =>
      match fn.name with
      | some fnName =>
          fnName == name && fn.params.length == args.length &&
            FunctionDecl.isExternallyNamedFunction fn
      | none => false)
  match candidates.find? (fun fn =>
      match FunctionDecl.orderedArgs? fn args with
      | some orderedArgs =>
          match
              Parameters.matchArgsAllowingInternalFunctionNamesWithEnv?
                env fn.params orderedArgs with
          | some true => true
          | _ => false
      | none => false) with
  | some fn => do
      let orderedArgs ← FunctionDecl.orderedArgs? fn args
      some (fn, orderedArgs)
  | none => do
      -- Arity fallback: exclude candidates whose KNOWN arg types definitely
      -- mismatch (`Parameters.arityFallbackCompatible`) — same wrong-callee
      -- guard as the library direct-call fallback; accept-when-unknown is
      -- preserved.
      let fn ← candidates.find?
        (fun candidate =>
          match FunctionDecl.orderedArgs? candidate args with
          | some orderedArgs =>
              Parameters.arityFallbackCompatible env candidate.params
                orderedArgs
          | none => false)
      let orderedArgs ← FunctionDecl.orderedArgs? fn args
      some (fn, orderedArgs)

def FunctionDecl.singleReturnTy? (decl : FunctionDecl) : Option Ty :=
  match decl.returns with
  | [ret] => some ret.ty
  | _ => none

/-- EVENT-OVERLOAD (soundness): whether every emit argument's inferred type
    matches the candidate event's parameter shape — the lowering-time analogue
    of the typechecker's `EventSig.matchesCheckedArgs`, reusing the same
    env-based argument typing (`Expr.abiTyWithEnv?`) and the same shape
    equivalence (`Ty.matchesShape`) the internal-call overload resolution
    uses. -/
def EventDecl.matchesEmitArgsWithEnv (env : TypeEnv) (decl : EventDecl)
    (args : List Expr) : Bool :=
  let rec go : List EventParam -> List Expr -> Bool
    | [], [] => true
    | param :: params, arg :: rest =>
        (match Expr.abiTyWithEnv? env arg with
         | some argTy => Ty.matchesShape argTy param.ty
         | none => false) && go params rest
    | _, _ => false
  go decl.params args

/-- EVENT-OVERLOAD (soundness): resolve an OVERLOADED bare-name `emit` to its
    signature-mangled runtime-table key. solc allows same-scope event overloads
    (`event E(uint256)` and `event E(address)` — error 5883 only rejects EQUAL
    parameter types), resolving each `emit E(...)` by argument types; the
    runtime event table was NAME-keyed, so every `emit E(...)` bound the FIRST
    decl named `E` → wrong topic0 (keccak of the wrong canonical signature) or
    a spurious arity/type mismatch revert. Returns `none` (leave the emit
    untouched — byte-identical) unless the name has ≥ 2 in-scope decls, all
    args are positional, and either arity or env-typed argument matching picks
    a UNIQUE candidate; the key is that candidate's canonical ABI signature
    (e.g. `"E(uint256)"` — parentheses can never collide with a Solidity
    identifier or a `.`-joined qualified key), which the contract assembly
    registers alongside the name-keyed entries. -/
def EventDecls.resolveOverloadedEmitKey? (events : List EventDecl)
    (env : TypeEnv) (name : Name) (args : List Arg) : Option Name := do
  let named := events.filter (fun e => e.name == name)
  if named.length < 2 then
    none
  else do
    let exprs ←
      mapOption
        (fun (arg : Arg) =>
          match arg with
          | Arg.positional expr => some expr
          | Arg.named _ _ => none)
        args
    let sameArity := named.filter (fun e => e.params.length == exprs.length)
    let chosen ←
      match sameArity with
      | [single] => some single
      | [] => none
      | _ =>
          match sameArity.filter
              (fun e => EventDecl.matchesEmitArgsWithEnv env e exprs) with
          | [single] => some single
          | _ => none
    EventDecl.abiSignature? chosen

/-- EVENT-OVERLOAD (soundness): the statement walk rewriting overloaded
    bare-name emits to their signature-mangled keys. Threads the local
    `TypeEnv` exactly as `Stmt.annotateAbiInSeqFuel` does (`varDecl` extends,
    loops/try/catch scope their bodies), so argument identifiers type against
    the bindings in scope at the emit site. Every statement other than a
    rewritten emit passes through structurally untouched, and an emit whose
    callee is not an overloaded in-scope event name is left byte-identical. -/
def Stmt.resolveOverloadedEventEmitsInSeqFuel :
    Nat -> List EventDecl -> TypeEnv -> Stmt -> Stmt × TypeEnv
  | 0, _, env, stmt => (stmt, env)
  | fuel + 1, events, env, stmt =>
      let recStmt (child : Stmt) : Stmt :=
        (Stmt.resolveOverloadedEventEmitsInSeqFuel fuel events env child).fst
      let recSeq (env : TypeEnv) (body : List Stmt) : List Stmt :=
        (body.foldl
          (fun (acc : List Stmt × TypeEnv) head =>
            let (done, env) := acc
            let (head', env') :=
              Stmt.resolveOverloadedEventEmitsInSeqFuel fuel events env head
            (head' :: done, env'))
          (([] : List Stmt), env)).fst.reverse
      let recClause : CatchClause -> CatchClause
        | CatchClause.clause name params body =>
            let clauseEnv := Parameters.extendTypeEnv "_catch" env params
            CatchClause.clause name params
              ((Stmt.resolveOverloadedEventEmitsInSeqFuel
                fuel events clauseEnv body).fst)
      match stmt with
      | Stmt.emitEvent (Expr.call (Expr.ident name) args) =>
          (match EventDecls.resolveOverloadedEmitKey? events env name args with
           | some key =>
               (Stmt.emitEvent (Expr.call (Expr.ident key) args), env)
           | none => (stmt, env))
      | Stmt.block body => (Stmt.block (recSeq env body), env)
      | Stmt.varDecl bindings init =>
          (Stmt.varDecl bindings init, VarBindings.extendTypeEnv env bindings)
      | Stmt.ifElse cond thenBranch elseBranch =>
          (Stmt.ifElse cond (recStmt thenBranch) (elseBranch.map recStmt), env)
      | Stmt.whileLoop cond body => (Stmt.whileLoop cond (recStmt body), env)
      | Stmt.doWhile body cond => (Stmt.doWhile (recStmt body) cond, env)
      | Stmt.forLoop init cond post body =>
          let (init', loopEnv) :=
            match init with
            | some initStmt =>
                let (stmt', env') :=
                  Stmt.resolveOverloadedEventEmitsInSeqFuel
                    fuel events env initStmt
                (some stmt', env')
            | none => (none, env)
          (Stmt.forLoop init' cond post
            ((Stmt.resolveOverloadedEventEmitsInSeqFuel
              fuel events loopEnv body).fst), env)
      | Stmt.tryCatch expr clauses =>
          (Stmt.tryCatch expr (clauses.map recClause), env)
      | Stmt.tryCatchReturns expr returns success clauses =>
          let successEnv := Parameters.extendTypeEnv "_try" env returns
          (Stmt.tryCatchReturns expr returns
            ((Stmt.resolveOverloadedEventEmitsInSeqFuel
              fuel events successEnv success).fst)
            (clauses.map recClause), env)
      | Stmt.unchecked body => (Stmt.unchecked (recStmt body), env)
      | other => (other, env)

def Stmt.resolveOverloadedEventEmits (events : List EventDecl)
    (env : TypeEnv) (stmt : Stmt) : Stmt :=
  (Stmt.resolveOverloadedEventEmitsInSeqFuel
    defaultAnnotateAbiFuel events env stmt).fst

/-- Generalized storage-ref-return gate: the callee value-returns a SINGLE
    `storage`-located reference, with NO body-shape requirement. The historical
    whole-param-only gate (LIB-STORAGE-RETURN-USE #156: `return s;` of a bare
    storage-ref parameter as the last statement — removed as dead code)
    pre-dates the R3 (#188) runtime re-pointing,
    which resolves a returned storage pointer from nested paths (`return o.d;`,
    `return a[i];`), storage LOCALS (`S storage p = s; return p;`) and
    conditional/early returns onto the caller's own storage — all pinned
    against the real EVM in `tests/forge-harness/storage-return-subfield-ops`
    (member/local/conditional callee shapes × mapping/array-field/plain-field
    uses). The struct-member→index rewrite and the call-result USE arms
    therefore gate on this predicate; the callee resolution machinery
    (`internalSingleStorageReturnRefCore?`, `returnStorageRefs == [true]`)
    still declines any callee whose single return is not actually threaded as
    a storage ref, so a widened rewrite can only reach the ref-capture path
    with a genuine storage pointer. -/
def FunctionDecl.returnsSingleStorageRef? (decl : FunctionDecl) : Bool :=
  match decl.returns with
  | [ret] => ret.location == some DataLocation.storage
  | _ => false

/-- Resolve an internal call site's callee (contract functions first, then free
    functions) purely for the storage-ref-return gate above. -/
def FunctionDecl.callSiteReturnsSingleStorageRef?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (name : Name) (args : List Arg) : Bool :=
  match FunctionDecl.findInternalCalleeWithArgs? functions env name args with
  | some (callee, _) => FunctionDecl.returnsSingleStorageRef? callee
  | none =>
      match FunctionDecl.findInternalCalleeWithArgs? freeFunctions env name args with
      | some (callee, _) => FunctionDecl.returnsSingleStorageRef? callee
      | none => false

def FunctionDecl.findInternalCalleeReturnTyWithArgs?
    (functions : List FunctionDecl) (env : TypeEnv)
    (name : Name) (args : List Arg) : Option Ty := do
  let (callee, _) ←
    FunctionDecl.findInternalCalleeWithArgs? functions env name args
  FunctionDecl.singleReturnTy? callee

/-- All return types of a resolvable internal callee (contract functions first,
    then free functions). Used by the nested-tuple-assignment RHS hoisting (R1)
    to size the per-return temps when a MULTI-return internal call fills a nested
    LHS target — `((a, b), c) = (foo(), bar())` where `foo` returns a 2-tuple. -/
def FunctionDecl.internalCalleeReturnTys?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (name : Name) (args : List Arg) : Option (List Ty) :=
  match FunctionDecl.findInternalCalleeWithArgs? functions env name args with
  | some (callee, _) => some (callee.returns.map (·.ty))
  | none =>
      match FunctionDecl.findInternalCalleeWithArgs? freeFunctions env name args with
      | some (callee, _) => some (callee.returns.map (·.ty))
      | none => none

/-- Single return type of a direct-call argument: a resolvable internal callee
    OR (stage C) a call through an internal function pointer, whose return type
    comes from the fn-typed variable's TYPE. Used by the call-argument hoisting
    gates so a ptr call nested in argument position hoists exactly like a
    direct call (the hoisted call itself routes through
    `ptrBoundaryCallParts?`). -/
def FunctionDecl.directOrPtrCallArgReturnTy?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (name : Name) (args : List Arg) : Option Ty :=
  match FunctionDecl.findInternalCalleeWithArgs? functions env name args with
  | some (callee, _) => FunctionDecl.singleReturnTy? callee
  | none =>
      match FunctionDecl.findInternalCalleeWithArgs? freeFunctions env name args with
      | some (callee, _) => FunctionDecl.singleReturnTy? callee
      | none =>
      match Expr.abiTyWithEnv? env (Expr.ident name) with
      | some (Ty.functionWithLocations _ _ [returnTy] _ _
          Visibility.internal_) => some returnTy
      | some (Ty.functionWithLocations _ _ [returnTy] _ _
          Visibility.private_) => some returnTy
      | _ => none

def Expr.abiTyWithInternalFunctionsEnv?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (expr : Expr) : Option Ty :=
  match Expr.abiTyWithEnv? env expr with
  | some ty => some ty
  | none =>
      match expr with
      | Expr.call (Expr.ident name) args =>
          match
              FunctionDecl.findInternalCalleeReturnTyWithArgs?
                functions env name args with
          | some ty => some ty
          | none =>
              match
                  FunctionDecl.findInternalCalleeReturnTyWithArgs?
                    freeFunctions env name args with
              | some ty => some ty
              | none =>
                  -- Stage C: a call through an internal function POINTER —
                  -- `name` is a fn-typed local/param/state var; its single
                  -- return type comes from the function TYPE.
                  match Expr.abiTyWithEnv? env (Expr.ident name) with
                  | some (Ty.functionWithLocations _ _ [returnTy] _ _
                      Visibility.internal_) => some returnTy
                  | some (Ty.functionWithLocations _ _ [returnTy] _ _
                      Visibility.private_) => some returnTy
                  | _ => none
      | Expr.call (Expr.typeName ty) [Arg.positional _] => some ty
      | Expr.call callee _ =>
          -- Call through an internal function POINTER whose callee is NOT a bare
          -- identifier (e.g. an element of a function-pointer array: `arr[i](x)`,
          -- or a fn pointer RETURNED by an internal call: `pick(true)(x)`).
          -- The result type is the pointer type's single return type. Type the
          -- callee with the internal-functions variant so a call-valued callee
          -- (a returned pointer) resolves too. External pointers / non-function
          -- callees fall through to `none`.
          match
              Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env callee with
          | some (Ty.functionWithLocations _ _ [returnTy] _ _
              Visibility.internal_) => some returnTy
          | some (Ty.functionWithLocations _ _ [returnTy] _ _
              Visibility.private_) => some returnTy
          | _ => none
      | Expr.payableConversion _ => some (Ty.address true)
      | Expr.unary UnaryOp.bitNot inner =>
          Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env inner
      | Expr.unary UnaryOp.neg inner =>
          Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env inner
      | Expr.unary UnaryOp.preIncrement inner
      | Expr.unary UnaryOp.preDecrement inner
      | Expr.unary UnaryOp.postIncrement inner
      | Expr.unary UnaryOp.postDecrement inner =>
          Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env inner
      | Expr.assign lhs _ _ =>
          Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env lhs
      | Expr.binary op lhs _ =>
          match op with
          | BinaryOp.lt | BinaryOp.gt | BinaryOp.le | BinaryOp.ge
          | BinaryOp.eq | BinaryOp.ne
          | BinaryOp.boolAnd | BinaryOp.boolOr => some Ty.bool
          | _ =>
              Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env lhs
      | Expr.ternary _ thenExpr _ =>
          Expr.abiTyWithInternalFunctionsEnv?
            functions freeFunctions env thenExpr
      | Expr.member base "balance" => do
          let _ ←
            Expr.abiTyWithInternalFunctionsEnv?
              functions freeFunctions env base
          some (Ty.uint 256)
      | Expr.member base "code" => do
          let _ ←
            Expr.abiTyWithInternalFunctionsEnv?
              functions freeFunctions env base
          some Ty.bytes
      | Expr.member base "codehash" => do
          let _ ←
            Expr.abiTyWithInternalFunctionsEnv?
              functions freeFunctions env base
          some (Ty.bytesN 32)
      | Expr.member base "length" => do
          let _ ←
            Expr.abiTyWithInternalFunctionsEnv?
              functions freeFunctions env base
          some (Ty.uint 256)
      | Expr.member base "selector" => do
          match
              Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env base with
          | some (Ty.functionWithLocations _ _ _ _ _ Visibility.external_) =>
              some (Ty.bytesN 4)
          | _ => none
      | Expr.member base "address" => do
          match
              Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env base with
          | some (Ty.functionWithLocations _ _ _ _ _ Visibility.external_) =>
              some (Ty.address false)
          | _ => none
      | Expr.index base indexExpr => do
          let baseTy ←
            Expr.abiTyWithInternalFunctionsEnv?
              functions freeFunctions env base
          match Ty.fixedBytesSize? baseTy with
          | some _ => some (Ty.bytesN 1)
          | none =>
              match baseTy with
              | Ty.bytes => some (Ty.bytesN 1)
              | Ty.array elementTy _ => some elementTy
              | Ty.mapping _ valueTy => some valueTy
              | Ty.tuple elements => do
                  let index ← Expr.numberLiteralNat? indexExpr
                  listGet? elements index
              | Ty.struct _ elements => do
                  let index ← Expr.numberLiteralNat? indexExpr
                  listGet? elements index
              | _ => none
      | Expr.slice base _ _ => do
          match
              Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env base with
          | some Ty.bytes => some Ty.bytes
          | some Ty.string => some Ty.string
          | some (Ty.array elementTy _) =>
              some (Ty.array elementTy none)
          | _ => none
      | _ => none
termination_by expr

-- Hoist-temp types for a literal-tuple variable DECLARATION whose RHS components
-- may be internal calls (`(uint a, , uint c) = (f(), g(), h(3))`). One type per
-- (binding, RHS-item) pair, in lockstep. A NAMED binding contributes its declared
-- type; an anonymous (hole) binding declares no type, so its discarded component
-- still must be evaluated into a temp — infer that temp's type from the RHS item
-- itself (`Expr.abiTyWithInternalFunctionsEnv?`). `VarBindings.sourceTysIncluding-
-- Anonymous?` cannot serve here: it fails outright on a typeless hole binding,
-- which collapsed the whole Stage-B declaration lowering to `none` (→ Panic 0).
def VarBindings.tupleDeclItemTysWithEnv?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv) :
    List VarBinding -> List TupleItem -> Option (List Ty)
  | [], [] => some []
  | binding :: bs, item :: its => do
      let ty ←
        match binding.ty with
        | some t => some t
        | none =>
            match item with
            | TupleItem.value expr =>
                Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env expr
            | TupleItem.hole => none
      let tail :=
        VarBindings.tupleDeclItemTysWithEnv? functions freeFunctions env bs its
      tail.map (fun rest => ty :: rest)
  | _, _ => none

def Parameter.matchesArgWithInternalFunctions?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (param : Parameter) (arg : Expr) : Option Bool := do
  let argTy ←
    Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env arg
  -- Argument passing (including using-for additional args and the re-checked
  -- receiver) uses DIRECTIONAL implicit convertibility: the argument must be
  -- convertible TO the parameter type, e.g. a `uint8` arg binds a `uint256`
  -- parameter (widened). Wider→narrower and incompatible/signedness mismatches
  -- stay rejected because `canImplicitlyConvert` is directional.
  --
  -- USINGFOR-WIDEN-BIND regression fix: `canImplicitlyConvert` only handles
  -- value-type widening (its struct/user arms are limited to exact `==`), so a
  -- storage struct / user-named / array / mapping receiver-or-arg — whose
  -- reflected `abiTy` (a `Ty.user`/`Ty.struct` with possibly a different
  -- namespace-qualified path than the parameter's resolved type) never `==`s the
  -- parameter type — stopped binding, breaking library flows like OpenZeppelin
  -- EnumerableMap. Fall back to nominal shape-matching (`Ty.matchesShape`, the
  -- pre-#158 predicate) for those cases. This is purely additive: the widening
  -- cases succeed via `canImplicitlyConvert`, and every `canImplicitlyConvert`
  -- reject (wider→narrower, uint→bytes, signedness) is ALSO a `matchesShape`
  -- reject, so no over-accept is reintroduced.
  some (Ty.canImplicitlyConvert argTy param.ty || Ty.matchesShape argTy param.ty)

def Parameter.matchesArgAllowingInternalFunctionNameWithFunctions?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (param : Parameter) (arg : Expr) : Option Bool :=
  match param.ty, arg with
  | Ty.functionWithLocations _ _ _ _ _ Visibility.internal_, Expr.ident _ =>
      some true
  | _, _ =>
      Parameter.matchesArgWithInternalFunctions?
        functions freeFunctions env param arg

def Parameters.matchArgsAllowingInternalFunctionNamesWithFunctionsEnv?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv) :
    List Parameter -> List Expr -> Option Bool
  | [], [] => some true
  | param :: params, arg :: args => do
      let head ←
        Parameter.matchesArgAllowingInternalFunctionNameWithFunctions?
          functions freeFunctions env param arg
      let tail ←
        Parameters.matchArgsAllowingInternalFunctionNamesWithFunctionsEnv?
          functions freeFunctions env params args
      some (head && tail)
  | _, _ => some false

structure InternalFunctionAliasBinding where
  «alias» : Name
  expected : Ty
  target : Option Name
  deriving Repr

abbrev InternalFunctionAliasEnv := List InternalFunctionAliasBinding

def InternalFunctionAliasEnv.lookup? (env : InternalFunctionAliasEnv)
    (name : Name) : Option InternalFunctionAliasBinding :=
  match env with
  | [] => none
  | binding :: rest =>
      if binding.«alias» == name then
        some binding
      else
        InternalFunctionAliasEnv.lookup? rest name

def InternalFunctionAliasEnv.target? (env : InternalFunctionAliasEnv)
    (name : Name) : Option Name :=
  match InternalFunctionAliasEnv.lookup? env name with
  | some binding => binding.target
  | none => none

def InternalFunctionAliasEnv.remove (env : InternalFunctionAliasEnv)
    (name : Name) : InternalFunctionAliasEnv :=
  env.filter (fun binding => binding.«alias» != name)

def InternalFunctionAliasEnv.extend (env : InternalFunctionAliasEnv)
    (binding : InternalFunctionAliasBinding) :
    InternalFunctionAliasEnv :=
  binding :: InternalFunctionAliasEnv.remove env binding.«alias»

def InternalFunctionAliasEnv.resolveFuel :
    Nat -> InternalFunctionAliasEnv -> Name -> Name
  | 0, _, name => name
  | fuel + 1, env, name =>
      match InternalFunctionAliasEnv.target? env name with
      | some target => InternalFunctionAliasEnv.resolveFuel fuel env target
      | none => name

def InternalFunctionAliasEnv.resolve (env : InternalFunctionAliasEnv)
    (name : Name) : Name :=
  InternalFunctionAliasEnv.resolveFuel 64 env name

def FunctionDecl.internalFunctionValueTy? (decl : FunctionDecl) :
    Option Ty :=
  match decl.kind, decl.name, decl.visibility with
  | FunctionKind.function, some _, some Visibility.external_ => none
  | FunctionKind.function, some _, _ =>
      some
        (Ty.functionWithLocations
          (decl.params.map Parameter.ty)
          (decl.params.map Parameter.location)
          (decl.returns.map Parameter.ty)
          (decl.returns.map Parameter.location)
          decl.mutability Visibility.internal_)
  | _, _, _ => none

def FunctionDecl.matchesInternalFunctionAliasTarget
    (expected : Ty) (targetName : Name) (decl : FunctionDecl) : Bool :=
  match decl.name, FunctionDecl.internalFunctionValueTy? decl with
  | some declName, some actual =>
      declName == targetName && Ty.canImplicitlyConvert actual expected
  | _, _ => false

def FunctionDecls.findInternalFunctionAliasTarget? (expected : Ty)
    (targetName : Name) : List FunctionDecl -> Option Name
  | [] => none
  | decl :: rest =>
      if FunctionDecl.matchesInternalFunctionAliasTarget
          expected targetName decl then
        decl.name
      else
        FunctionDecls.findInternalFunctionAliasTarget?
          expected targetName rest

def FunctionDecls.findInternalFunctionAliasTargetIn?
    (functions freeFunctions : List FunctionDecl) (expected : Ty)
    (targetName : Name) : Option Name :=
  match
      FunctionDecls.findInternalFunctionAliasTarget?
        expected targetName functions with
  | some resolved => some resolved
  | none =>
      FunctionDecls.findInternalFunctionAliasTarget?
        expected targetName freeFunctions

def InternalFunctionAliasEnv.aliasTarget? (aliasEnv : InternalFunctionAliasEnv)
    (functions freeFunctions : List FunctionDecl) (expected : Ty)
    (sourceName : Name) : Option Name :=
  let sourceName := InternalFunctionAliasEnv.resolve aliasEnv sourceName
  FunctionDecls.findInternalFunctionAliasTargetIn?
    functions freeFunctions expected sourceName

def VarBinding.internalFunctionAliasTarget?
    (aliasEnv : InternalFunctionAliasEnv)
    (functions freeFunctions : List FunctionDecl)
    (binding : VarBinding) (sourceName : Name) :
    Option InternalFunctionAliasBinding := do
  let aliasName ← binding.name
  let expected ← binding.ty
  match expected with
  | Ty.functionWithLocations _ _ _ _ _ Visibility.internal_ =>
      let target ←
        InternalFunctionAliasEnv.aliasTarget?
          aliasEnv functions freeFunctions expected sourceName
      some
        { «alias» := aliasName
          expected := expected
          target := some target }
  | _ => none

def VarBinding.internalFunctionAliasDecl?
    (binding : VarBinding) : Option InternalFunctionAliasBinding := do
  let aliasName ← binding.name
  let expected ← binding.ty
  match expected with
  | Ty.functionWithLocations _ _ _ _ _ Visibility.internal_ =>
      some
        { «alias» := aliasName
          expected := expected
          target := none }
  | _ => none

def InternalFunctionAliasEnv.reassignedTarget?
    (aliasEnv : InternalFunctionAliasEnv)
    (functions freeFunctions : List FunctionDecl)
    (aliasName sourceName : Name) :
    Option InternalFunctionAliasBinding := do
  let binding ← InternalFunctionAliasEnv.lookup? aliasEnv aliasName
  let target ←
    InternalFunctionAliasEnv.aliasTarget?
      aliasEnv functions freeFunctions binding.expected sourceName
  some { binding with target := some target }

def InternalFunctionAliasEnv.deletedTarget?
    (aliasEnv : InternalFunctionAliasEnv)
    (aliasName : Name) : Option InternalFunctionAliasBinding := do
  let binding ← InternalFunctionAliasEnv.lookup? aliasEnv aliasName
  some { binding with target := none }

def VarBinding.removeInternalFunctionAlias
    (aliasEnv : InternalFunctionAliasEnv)
    (binding : VarBinding) : InternalFunctionAliasEnv :=
  match binding.name with
  | some name => InternalFunctionAliasEnv.remove aliasEnv name
  | none => aliasEnv

def VarBindings.removeInternalFunctionAliases :
    InternalFunctionAliasEnv -> List VarBinding -> InternalFunctionAliasEnv
  | aliasEnv, [] => aliasEnv
  | aliasEnv, binding :: rest =>
      VarBindings.removeInternalFunctionAliases
        (VarBinding.removeInternalFunctionAlias aliasEnv binding) rest

def Parameter.internalFunctionAliasArg?
    (aliasEnv : InternalFunctionAliasEnv)
    (functions freeFunctions : List FunctionDecl)
    (fallbackPrefix : String) (index : Nat)
    (param : Parameter) (arg : Expr) :
    Option InternalFunctionAliasBinding := do
  let expected := param.ty
  match expected, arg with
  | Ty.functionWithLocations _ _ _ _ _ Visibility.internal_,
      Expr.ident sourceName =>
      let aliasName := param.name.getD (fallbackPrefix ++ toString index)
      if sourceName == internalFunctionPointerPanicName then
        some
          { «alias» := aliasName
            expected := expected
            target := none }
      else
        let target ←
          InternalFunctionAliasEnv.aliasTarget?
            aliasEnv functions freeFunctions expected sourceName
        some
          { «alias» := aliasName
            expected := expected
            target := some target }
  | _, _ => none

def Parameter.isInternalFunction (param : Parameter) : Bool :=
  match param.ty with
  | Ty.functionWithLocations _ _ _ _ _ Visibility.internal_ => true
  | _ => false

def internalCallArgTempName (fallbackPrefix : String) (index : Nat) : Name :=
  fallbackPrefix ++ "_eval" ++ toString index

def Arg.directInternalCall? : Arg -> Option (Name × List Arg)
  | Arg.positional (Expr.call (Expr.ident name) args) => some (name, args)
  | Arg.named _ (Expr.call (Expr.ident name) args) => some (name, args)
  | _ => none

/-- #173 TERNARY-CALL-IN-ARG: a ternary argument `cond ? thenE : elseE`. When a
    branch (or the condition) contains a non-pure call, the pure argument
    lowering can't lower it; the call-argument hoister routes it through the same
    guarded-branch ternary-call hoister used for binary operands / conditions /
    returns (`internalExprSingleReturnUseCore?`), binding the ternary result to a
    temp. A ternary with pure branches makes that hoister decline (`none`), so
    the caller falls back to the pure path unchanged. -/
def Arg.ternaryParts? : Arg -> Option (Expr × Expr × Expr)
  | Arg.positional (Expr.ternary cond thenE elseE) => some (cond, thenE, elseE)
  | Arg.named _ (Expr.ternary cond thenE elseE) => some (cond, thenE, elseE)
  | _ => none

def Arg.withExpr (expr : Expr) : Arg -> Arg
  | Arg.positional _ => Arg.positional expr
  | Arg.named name _ => Arg.named name expr

def Args.replaceDirectInternalCallArg? (fallbackPrefix : String) :
    Nat -> List Arg -> Option (Name × List Arg × Name × List Arg)
  | _, [] => none
  | index, arg :: rest =>
      let tempName := internalCallArgTempName fallbackPrefix index
      match Arg.directInternalCall? arg with
      | some (name, args) =>
          some
            ( name
            , args
            , tempName
            , Arg.withExpr (Expr.ident tempName) arg :: rest )
      | none => do
          let (name, args, foundTemp, rest') ←
            Args.replaceDirectInternalCallArg? fallbackPrefix (index + 1) rest
          some (name, args, foundTemp, arg :: rest')

def Parameter.toStorageAwareCoreArgDeclsEvaluated?
    (storageRefEnv : StorageRefEnv) (storageNames : List Name)
    (env : TypeEnv) (fallbackPrefix : String)
    (index : Nat) (param : Parameter) (arg : Expr) :
    Option (List CoreStmt) := do
  match param.location with
  | some DataLocation.storage => do
      let coreStmt ←
        Parameter.toStorageAwareCoreArgDecl?
          storageRefEnv storageNames env fallbackPrefix index param arg
      some [coreStmt]
  | _ => do
      let tempName := internalCallArgTempName fallbackPrefix index
      let tempParam := { param with name := some tempName }
      let tempDecl ←
        Parameter.toStorageAwareCoreArgDecl?
          storageRefEnv storageNames env fallbackPrefix index tempParam arg
      let paramDecl ←
        Parameter.toStorageAwareCoreArgDecl?
          storageRefEnv storageNames env fallbackPrefix index param
          (Expr.ident tempName)
      some [tempDecl, paramDecl]

def Parameter.toStorageAwareCoreArgDeclPiecesEvaluated?
    (storageRefEnv : StorageRefEnv) (storageNames : List Name)
    (env : TypeEnv) (fallbackPrefix : String)
    (index : Nat) (param : Parameter) (arg : Expr) :
    Option (List CoreStmt × List CoreStmt) := do
  match param.location with
  | some DataLocation.storage => do
      let coreStmt ←
        Parameter.toStorageAwareCoreArgDecl?
          storageRefEnv storageNames env fallbackPrefix index param arg
      some ([], [coreStmt])
  | _ => do
      let tempName := internalCallArgTempName fallbackPrefix index
      let tempParam := { param with name := some tempName }
      let tempDecl ←
        Parameter.toStorageAwareCoreArgDecl?
          storageRefEnv storageNames env fallbackPrefix index tempParam arg
      let paramDecl ←
        Parameter.toStorageAwareCoreArgDecl?
          storageRefEnv storageNames env fallbackPrefix index param
          (Expr.ident tempName)
      some ([tempDecl], [paramDecl])

def Parameters.toStorageAwareCoreArgDeclPiecesWithInternalAliasesFrom?
    (storageRefEnv : StorageRefEnv) (storageNames : List Name)
    (env : TypeEnv)
    (functions freeFunctions : List FunctionDecl)
    (fallbackPrefix : String) :
    Nat -> InternalFunctionAliasEnv -> List Parameter -> List Expr ->
    Option (InternalFunctionAliasEnv × List CoreStmt × List CoreStmt)
  | _, aliasEnv, [], [] => some (aliasEnv, [], [])
  | index, aliasEnv, param :: params, arg :: args =>
      match
          Parameter.internalFunctionAliasArg?
            aliasEnv functions freeFunctions fallbackPrefix index param arg with
      | some binding => do
          let aliasEnv' := InternalFunctionAliasEnv.extend aliasEnv binding
          Parameters.toStorageAwareCoreArgDeclPiecesWithInternalAliasesFrom?
            storageRefEnv storageNames env functions freeFunctions
            fallbackPrefix (index + 1) aliasEnv' params args
      | none => do
          if Parameter.isInternalFunction param then
            none
          else
            let (headArgDecls, headParamDecls) ←
              Parameter.toStorageAwareCoreArgDeclPiecesEvaluated?
                storageRefEnv storageNames env fallbackPrefix index param arg
            let (aliasEnv', tailArgDecls, tailParamDecls) ←
              Parameters.toStorageAwareCoreArgDeclPiecesWithInternalAliasesFrom?
                storageRefEnv storageNames env functions freeFunctions
                fallbackPrefix (index + 1) aliasEnv params args
            some
              ( aliasEnv'
              , headArgDecls ++ tailArgDecls
              , headParamDecls ++ tailParamDecls )
  | _, _, _, _ => none

/-- Does statement `s` reassign (`name = …`) or `delete name` a local internal
    function-pointer named `name` anywhere within its subtree? Used to decide
    whether a `function(...) internal name = target;` var declaration may be
    statically inlined as an alias: if the name is rebound inside a NESTED
    control-flow construct (an `if`/loop/`try` branch, or a bare block), the
    static alias would be resolved against the WRONG (declaration-time) target
    at a later call site, because the alias-inlining sequence fold discards the
    per-branch environment. In that case the alias is declined and `name`
    stays a genuine runtime pointer local, so the call lowers to
    `Stmt.internalCallPtr` and dispatches on the real (possibly zeroed)
    dispatch ID — matching solc's `Panic(0x51)` for a deleted/uninitialized
    pointer. Fuel-bounded (mirrors the alias-inlining passes); fuel exhaustion
    conservatively reports `true` (decline the alias — always sound). -/
def Stmt.internalFunctionAliasNameReboundFuel (name : Name) :
    Nat -> Stmt -> Bool
  | 0, _ => true
  | _ + 1, Stmt.expr (Expr.assign (Expr.ident n) _ _) => n == name
  | _ + 1, Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident n)) => n == name
  | fuel + 1, Stmt.block body =>
      body.any (Stmt.internalFunctionAliasNameReboundFuel name fuel)
  | fuel + 1, Stmt.ifElse _ thenBranch elseBranch =>
      Stmt.internalFunctionAliasNameReboundFuel name fuel thenBranch ||
        (match elseBranch with
         | some s => Stmt.internalFunctionAliasNameReboundFuel name fuel s
         | none => false)
  | fuel + 1, Stmt.whileLoop _ body =>
      Stmt.internalFunctionAliasNameReboundFuel name fuel body
  | fuel + 1, Stmt.doWhile body _ =>
      Stmt.internalFunctionAliasNameReboundFuel name fuel body
  | fuel + 1, Stmt.forLoop init _ _ body =>
      (match init with
       | some s => Stmt.internalFunctionAliasNameReboundFuel name fuel s
       | none => false) ||
        Stmt.internalFunctionAliasNameReboundFuel name fuel body
  | fuel + 1, Stmt.unchecked body =>
      Stmt.internalFunctionAliasNameReboundFuel name fuel body
  | fuel + 1, Stmt.tryCatch _ clauses =>
      clauses.any (fun clause =>
        match clause with
        | CatchClause.clause _ _ body =>
            Stmt.internalFunctionAliasNameReboundFuel name fuel body)
  | fuel + 1, Stmt.tryCatchReturns _ _ success clauses =>
      Stmt.internalFunctionAliasNameReboundFuel name fuel success ||
        clauses.any (fun clause =>
          match clause with
          | CatchClause.clause _ _ body =>
              Stmt.internalFunctionAliasNameReboundFuel name fuel body)
  | _ + 1, _ => false
termination_by fuel _ => fuel

/-- The alias name is rebound inside a NESTED construct somewhere in the rest of
    the scope. Top-level `name = <ident>` reassignments and top-level
    `delete name` statements are handled correctly by the sequence fold itself
    (they update the alias in the unconditional control-flow position), so they
    are NOT counted here — only reassignments/deletes reachable by descending
    into a compound statement invalidate the static alias. -/
def Stmt.internalFunctionAliasNameReboundInRest
    (name : Name) (rest : List Stmt) : Bool :=
  rest.any (fun s =>
    match s with
    -- The sequence fold can update a static alias only for a bare-function
    -- RHS (`ptr = f`).  Any other top-level reassignment of THIS alias must
    -- keep the declaration as a real runtime pointer.  Otherwise the fold
    -- erases the declaration, retains the old/uninitialised alias binding,
    -- and rewrites the assignment LHS itself (for example `ptr = L.f`) into
    -- the panic sentinel.
    | Stmt.expr
        (Expr.assign (Expr.ident _) _ (Expr.ident _)) =>
        false
    | Stmt.expr (Expr.assign (Expr.ident assigned) _ _) => assigned == name
    | Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident _)) => false
    | _ => Stmt.internalFunctionAliasNameReboundFuel name 1024 s)

set_option maxHeartbeats 1000000 in
mutual

def Expr.inlineInternalFunctionAliasesFuel :
    Nat -> InternalFunctionAliasEnv -> Expr -> Expr
  | 0, _, expr => expr
  | _ + 1, _, Expr.literal literal => Expr.literal literal
  | _ + 1, aliasEnv, Expr.ident name =>
      match InternalFunctionAliasEnv.lookup? aliasEnv name with
      | some binding =>
          match binding.target with
          | some _ =>
              Expr.ident (InternalFunctionAliasEnv.resolve aliasEnv name)
          -- An uninitialised internal function pointer is dispatch ID zero
          -- when used as a VALUE (comparison, assignment, return, container
          -- element).  Only CALLING it panics 0x51; the specialised call arms
          -- below retain that behaviour.
          | none => Expr.literal (Literal.number "0")
      | none => Expr.ident name
  | _ + 1, _, Expr.typeName ty => Expr.typeName ty
  | fuel + 1, aliasEnv, Expr.member base member =>
      Expr.member
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv base)
        member
  | fuel + 1, aliasEnv, Expr.index base index =>
      Expr.index
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv base)
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv index)
  | fuel + 1, aliasEnv, Expr.slice base start stop =>
      Expr.slice
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv base)
        (start.map
          (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv))
        (stop.map
          (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | fuel + 1, aliasEnv, Expr.call (Expr.ident name) args =>
      match InternalFunctionAliasEnv.lookup? aliasEnv name with
      | some binding =>
          match binding.target with
          | some _ =>
              Expr.call
                (Expr.ident (InternalFunctionAliasEnv.resolve aliasEnv name))
                (args.map
                  (Arg.inlineInternalFunctionAliasesFuel fuel aliasEnv))
          | none =>
              Expr.call (Expr.ident internalFunctionPointerPanicName) []
      | none =>
          Expr.call
            (Expr.ident name)
            (args.map
              (Arg.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | fuel + 1, aliasEnv, Expr.call fn args =>
      Expr.call
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv fn)
        (args.map
          (Arg.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | fuel + 1, aliasEnv, Expr.callWithOptions (Expr.ident name) options args =>
      match InternalFunctionAliasEnv.lookup? aliasEnv name with
      | some binding =>
          match binding.target with
          | some _ =>
              Expr.callWithOptions
                (Expr.ident
                  (InternalFunctionAliasEnv.resolve aliasEnv name))
                (options.map
                  (CallOption.inlineInternalFunctionAliasesFuel
                    fuel aliasEnv))
                (args.map
                  (Arg.inlineInternalFunctionAliasesFuel fuel aliasEnv))
          | none =>
              Expr.call (Expr.ident internalFunctionPointerPanicName) []
      | none =>
          Expr.callWithOptions
            (Expr.ident name)
            (options.map
              (CallOption.inlineInternalFunctionAliasesFuel fuel aliasEnv))
            (args.map
              (Arg.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | fuel + 1, aliasEnv, Expr.callWithOptions fn options args =>
      Expr.callWithOptions
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv fn)
        (options.map
          (CallOption.inlineInternalFunctionAliasesFuel fuel aliasEnv))
        (args.map
          (Arg.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | fuel + 1, aliasEnv, Expr.newExpr ty args =>
      Expr.newExpr ty
        (args.map
          (Arg.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | fuel + 1, aliasEnv, Expr.tuple items =>
      Expr.tuple
        (items.map
          (TupleItem.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | fuel + 1, aliasEnv, Expr.array exprs =>
      Expr.array
        (exprs.map
          (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | fuel + 1, aliasEnv, Expr.enumFromUInt maxValue inner =>
      Expr.enumFromUInt maxValue
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv inner)
  | fuel + 1, aliasEnv, Expr.unary op inner =>
      Expr.unary op
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv inner)
  | fuel + 1, aliasEnv, Expr.binary op lhs rhs =>
      Expr.binary op
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv lhs)
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv rhs)
  | fuel + 1, aliasEnv, Expr.ternary cond thenExpr elseExpr =>
      Expr.ternary
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv cond)
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv thenExpr)
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv elseExpr)
  | fuel + 1, aliasEnv, Expr.assign lhs op rhs =>
      Expr.assign
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv lhs)
        op
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv rhs)
  | fuel + 1, aliasEnv, Expr.payableConversion inner =>
      Expr.payableConversion
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv inner)
termination_by fuel _ _ => fuel

def Arg.inlineInternalFunctionAliasesFuel :
    Nat -> InternalFunctionAliasEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, aliasEnv, Arg.positional expr =>
      Arg.positional
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv expr)
  | fuel + 1, aliasEnv, Arg.named name expr =>
      Arg.named name
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv expr)
termination_by fuel _ _ => fuel

def CallOption.inlineInternalFunctionAliasesFuel :
    Nat -> InternalFunctionAliasEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, aliasEnv, CallOption.named name expr =>
      CallOption.named name
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv expr)
termination_by fuel _ _ => fuel

def TupleItem.inlineInternalFunctionAliasesFuel :
    Nat -> InternalFunctionAliasEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | _ + 1, _, TupleItem.hole => TupleItem.hole
  | fuel + 1, aliasEnv, TupleItem.value expr =>
      TupleItem.value
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv expr)
termination_by fuel _ _ => fuel

def Stmt.inlineInternalFunctionAliasesFuel
    (functions freeFunctions : List FunctionDecl) :
    Nat -> InternalFunctionAliasEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | _ + 1, _, Stmt.empty => Stmt.empty
  | fuel + 1, aliasEnv, Stmt.block body =>
      Stmt.block
        (Stmt.inlineInternalFunctionAliasSeqFuel
          functions freeFunctions fuel aliasEnv body).fst
  | fuel + 1, aliasEnv, Stmt.varDecl bindings init =>
      Stmt.varDecl bindings
        (init.map
          (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | fuel + 1, aliasEnv, Stmt.expr expr =>
      Stmt.expr
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv expr)
  | fuel + 1, aliasEnv, Stmt.ifElse cond thenBranch elseBranch =>
      Stmt.ifElse
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv cond)
        (Stmt.inlineInternalFunctionAliasesFuel
          functions freeFunctions fuel aliasEnv thenBranch)
        (elseBranch.map
          (Stmt.inlineInternalFunctionAliasesFuel
            functions freeFunctions fuel aliasEnv))
  | fuel + 1, aliasEnv, Stmt.whileLoop cond body =>
      Stmt.whileLoop
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv cond)
        (Stmt.inlineInternalFunctionAliasesFuel
          functions freeFunctions fuel aliasEnv body)
  | fuel + 1, aliasEnv, Stmt.doWhile body cond =>
      Stmt.doWhile
        (Stmt.inlineInternalFunctionAliasesFuel
          functions freeFunctions fuel aliasEnv body)
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv cond)
  | fuel + 1, aliasEnv, Stmt.forLoop init cond post body =>
      Stmt.forLoop
        (init.map
          (Stmt.inlineInternalFunctionAliasesFuel
            functions freeFunctions fuel aliasEnv))
        (cond.map
          (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv))
        (post.map
          (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv))
        (Stmt.inlineInternalFunctionAliasesFuel
          functions freeFunctions fuel aliasEnv body)
  | fuel + 1, aliasEnv, Stmt.tryCatch expr clauses =>
      Stmt.tryCatch
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv expr)
        (clauses.map
          (CatchClause.inlineInternalFunctionAliasesFuel
            functions freeFunctions fuel aliasEnv))
  | fuel + 1, aliasEnv, Stmt.tryCatchReturns expr returns success clauses =>
      Stmt.tryCatchReturns
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv expr)
        returns
        (Stmt.inlineInternalFunctionAliasesFuel
          functions freeFunctions fuel aliasEnv success)
        (clauses.map
          (CatchClause.inlineInternalFunctionAliasesFuel
            functions freeFunctions fuel aliasEnv))
  | fuel + 1, aliasEnv, Stmt.emitEvent expr =>
      Stmt.emitEvent
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv expr)
  | fuel + 1, aliasEnv, Stmt.revertCall expr =>
      Stmt.revertCall
        (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv expr)
  | fuel + 1, aliasEnv, Stmt.returnValues expr? =>
      Stmt.returnValues
        (expr?.map
          (Expr.inlineInternalFunctionAliasesFuel fuel aliasEnv))
  | _ + 1, _, Stmt.break => Stmt.break
  | _ + 1, _, Stmt.continue => Stmt.continue
  | fuel + 1, aliasEnv, Stmt.unchecked body =>
      Stmt.unchecked
        (Stmt.inlineInternalFunctionAliasesFuel
          functions freeFunctions fuel aliasEnv body)
  | _ + 1, _, Stmt.inlineAssembly code => Stmt.inlineAssembly code
  | _ + 1, _, Stmt.modifierPlaceholder => Stmt.modifierPlaceholder
termination_by fuel _ _ => fuel

def CatchClause.inlineInternalFunctionAliasesFuel
    (functions freeFunctions : List FunctionDecl) :
    Nat -> InternalFunctionAliasEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, aliasEnv, CatchClause.clause name params body =>
      CatchClause.clause name params
        (Stmt.inlineInternalFunctionAliasesFuel
          functions freeFunctions fuel aliasEnv body)
termination_by fuel _ _ => fuel

def Stmt.inlineInternalFunctionAliasSeqFuel
    (functions freeFunctions : List FunctionDecl) :
    Nat -> InternalFunctionAliasEnv ->
    List Stmt -> List Stmt × InternalFunctionAliasEnv
  | 0, aliasEnv, stmts => (stmts, aliasEnv)
  | fuel + 1, aliasEnv,
    Stmt.varDecl [binding] (some (Expr.ident sourceName)) :: rest =>
      match
          VarBinding.internalFunctionAliasTarget?
            aliasEnv functions freeFunctions binding sourceName with
      | some aliasBinding =>
          if (binding.name.map
                (fun n => Stmt.internalFunctionAliasNameReboundInRest n rest)).getD
              false then
            -- The alias name is rebound inside a nested branch/loop later in the
            -- scope; a static alias would resolve the trailing call to the
            -- declaration-time target. Decline: keep `name` a runtime pointer.
            let head :=
              Stmt.inlineInternalFunctionAliasesFuel functions freeFunctions
                fuel aliasEnv
                (Stmt.varDecl [binding] (some (Expr.ident sourceName)))
            let aliasEnv' :=
              VarBinding.removeInternalFunctionAlias aliasEnv binding
            let (tail, finalEnv) :=
              Stmt.inlineInternalFunctionAliasSeqFuel
                functions freeFunctions fuel aliasEnv' rest
            (head :: tail, finalEnv)
          else
          let aliasEnv' :=
            InternalFunctionAliasEnv.extend aliasEnv aliasBinding
          Stmt.inlineInternalFunctionAliasSeqFuel
            functions freeFunctions fuel aliasEnv' rest
      | none =>
          let head :=
            Stmt.inlineInternalFunctionAliasesFuel functions freeFunctions
              fuel aliasEnv
              (Stmt.varDecl [binding] (some (Expr.ident sourceName)))
          let aliasEnv' :=
            VarBinding.removeInternalFunctionAlias aliasEnv binding
          let (tail, finalEnv) :=
            Stmt.inlineInternalFunctionAliasSeqFuel
              functions freeFunctions fuel aliasEnv' rest
          (head :: tail, finalEnv)
  | fuel + 1, aliasEnv, Stmt.varDecl [binding] none :: rest =>
      match VarBinding.internalFunctionAliasDecl? binding with
      | some aliasBinding =>
          if (binding.name.map
                (fun n => Stmt.internalFunctionAliasNameReboundInRest n rest)).getD
              false then
            let head :=
              Stmt.inlineInternalFunctionAliasesFuel functions freeFunctions
                fuel aliasEnv (Stmt.varDecl [binding] none)
            let aliasEnv' :=
              VarBinding.removeInternalFunctionAlias aliasEnv binding
            let (tail, finalEnv) :=
              Stmt.inlineInternalFunctionAliasSeqFuel
                functions freeFunctions fuel aliasEnv' rest
            (head :: tail, finalEnv)
          else
          let aliasEnv' :=
            InternalFunctionAliasEnv.extend aliasEnv aliasBinding
          Stmt.inlineInternalFunctionAliasSeqFuel
            functions freeFunctions fuel aliasEnv' rest
      | none =>
          let head :=
            Stmt.inlineInternalFunctionAliasesFuel functions freeFunctions
              fuel aliasEnv (Stmt.varDecl [binding] none)
          let aliasEnv' :=
            VarBinding.removeInternalFunctionAlias aliasEnv binding
          let (tail, finalEnv) :=
            Stmt.inlineInternalFunctionAliasSeqFuel
              functions freeFunctions fuel aliasEnv' rest
          (head :: tail, finalEnv)
  | fuel + 1, aliasEnv,
    Stmt.expr
      (Expr.assign (Expr.ident aliasName) AssignOp.assign
        (Expr.ident sourceName)) :: rest =>
      match
          InternalFunctionAliasEnv.reassignedTarget?
            aliasEnv functions freeFunctions aliasName sourceName with
      | some aliasBinding =>
          let aliasEnv' :=
            InternalFunctionAliasEnv.extend aliasEnv aliasBinding
          Stmt.inlineInternalFunctionAliasSeqFuel
            functions freeFunctions fuel aliasEnv' rest
      | none =>
          let stmt :=
            Stmt.expr
              (Expr.assign (Expr.ident aliasName) AssignOp.assign
                (Expr.ident sourceName))
          let head :=
            Stmt.inlineInternalFunctionAliasesFuel
              functions freeFunctions fuel aliasEnv stmt
          let (tail, finalEnv) :=
            Stmt.inlineInternalFunctionAliasSeqFuel
              functions freeFunctions fuel aliasEnv rest
          (head :: tail, finalEnv)
  | fuel + 1, aliasEnv,
    Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident aliasName)) :: rest =>
      match InternalFunctionAliasEnv.deletedTarget? aliasEnv aliasName with
      | some aliasBinding =>
          let aliasEnv' :=
            InternalFunctionAliasEnv.extend aliasEnv aliasBinding
          Stmt.inlineInternalFunctionAliasSeqFuel
            functions freeFunctions fuel aliasEnv' rest
      | none =>
          let stmt :=
            Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident aliasName))
          let head :=
            Stmt.inlineInternalFunctionAliasesFuel
              functions freeFunctions fuel aliasEnv stmt
          let (tail, finalEnv) :=
            Stmt.inlineInternalFunctionAliasSeqFuel
              functions freeFunctions fuel aliasEnv rest
          (head :: tail, finalEnv)
  | fuel + 1, aliasEnv, Stmt.varDecl bindings init :: rest =>
      let head :=
        Stmt.inlineInternalFunctionAliasesFuel functions freeFunctions
          fuel aliasEnv (Stmt.varDecl bindings init)
      let aliasEnv' :=
        VarBindings.removeInternalFunctionAliases aliasEnv bindings
      let (tail, finalEnv) :=
        Stmt.inlineInternalFunctionAliasSeqFuel
          functions freeFunctions fuel aliasEnv' rest
      (head :: tail, finalEnv)
  | fuel + 1, aliasEnv, stmt :: rest =>
      let head :=
        Stmt.inlineInternalFunctionAliasesFuel
          functions freeFunctions fuel aliasEnv stmt
      let (tail, finalEnv) :=
        Stmt.inlineInternalFunctionAliasSeqFuel
          functions freeFunctions fuel aliasEnv rest
      (head :: tail, finalEnv)
  | _ + 1, aliasEnv, [] => ([], aliasEnv)
termination_by fuel _ _ => fuel

end

def defaultInternalFunctionAliasFuel : Nat := 1024

def Stmt.inlineInternalFunctionAliasesInBody
    (functions freeFunctions : List FunctionDecl) (stmt : Stmt) : Stmt :=
  Stmt.inlineInternalFunctionAliasesFuel
    functions freeFunctions defaultInternalFunctionAliasFuel [] stmt

inductive InternalFunctionPointerCallRewriteStatus where
  | resolved
  | panic
  | notFunctionPointerCall
  deriving Repr, BEq

def InternalFunctionAliasBinding.targetPair
    (binding : InternalFunctionAliasBinding) :
    Name × Option Name :=
  (binding.«alias», binding.target)

def InternalFunctionAliasEnv.targetPairs
    (env : InternalFunctionAliasEnv) :
    List (Name × Option Name) :=
  env.map InternalFunctionAliasBinding.targetPair

def Expr.storageRefArrayMemberStmtCore?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) :
    Expr -> Option CoreStmt
  | Expr.call (Expr.member target "push") [] => do
      let (source, indexes) ←
        Expr.storageRefPathCoreWithEnv? storageRefEnv storageNames env target
      match target with
      | Expr.ident name => do
          let ty ← TypeEnv.lookup? env name
          if Ty.hasStorageArrayMembers ty then
            some ()
          else
            none
      | _ => some ()
      match indexes with
      | [] =>
          some (SolidCore.Solidity.Source.Stmt.storageArrayPushRef source none)
      | _ =>
          some
            (SolidCore.Solidity.Source.Stmt.storageArrayPushRefPath
              source indexes none)
  | Expr.call (Expr.member target "push") [Arg.positional value] => do
      let (source, indexes) ←
        Expr.storageRefPathCoreWithEnv? storageRefEnv storageNames env target
      match target with
      | Expr.ident name => do
          let ty ← TypeEnv.lookup? env name
          if Ty.hasStorageArrayMembers ty then
            some ()
          else
            none
      | _ => some ()
      -- NARROW-PUSH (#183): lower the pushed value against the array ELEMENT
      -- type through the env-aware `toCoreAsWithEnv?`, so a narrow
      -- (`uintN`/`intN`) checked-arithmetic argument (`arr.push(a + c)`) keeps
      -- its operand-width `uintCleanup`/`intCleanup` (→ Panic 0x11 on overflow).
      -- The env-less `toCore?` dropped it and silently wrapped at 256 bits.
      -- A genuine explicit truncating cast (`arr.push(uint8(w))`) is NOT
      -- peeled by `toCoreAsWithEnv?` and still truncates.
      let valueCore ←
        match (match Expr.abiTyWithEnv? env target with
              | some (Ty.array elemTy _) => some elemTy
              | _ => none) with
        | some elemTy =>
            match Expr.toCoreAsWithEnv? storageNames env elemTy value with
            | some c => some c
            | none => Expr.toCore? storageNames value
        | none => Expr.toCore? storageNames value
      match indexes with
      | [] =>
          some
            (SolidCore.Solidity.Source.Stmt.storageArrayPushRef
              source (some valueCore))
      | _ =>
          some
            (SolidCore.Solidity.Source.Stmt.storageArrayPushRefPath
              source indexes (some valueCore))
  | Expr.call (Expr.member target "pop") [] => do
      let (source, indexes) ←
        Expr.storageRefPathCoreWithEnv? storageRefEnv storageNames env target
      match target with
      | Expr.ident name => do
          let ty ← TypeEnv.lookup? env name
          if Ty.hasStorageArrayMembers ty then
            some ()
          else
            none
      | _ => some ()
      match indexes with
      | [] =>
          some (SolidCore.Solidity.Source.Stmt.storageArrayPopRef source)
      | _ =>
          some
            (SolidCore.Solidity.Source.Stmt.storageArrayPopRefPath
              source indexes)
  | _ => none

def Expr.storageRefArrayPushAssignStmtCore?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (target : Expr) (rhs : Expr) :
    Option CoreStmt := do
  let (name, indexes) ←
    Expr.storageRefPathCoreWithEnv? storageRefEnv storageNames env target
  match target with
  | Expr.ident ident => do
      let ty ← TypeEnv.lookup? env ident
      if Ty.hasStorageArrayMembers ty then
        some ()
      else
        none
  | _ => some ()
  -- NARROW-PUSH (#183, indexed twin): lower the pushed value against the array
  -- element type via `toCoreAsWithEnv?` so narrow checked arithmetic Panics
  -- 0x11 on overflow (see the companion note in `storageRefArrayMemberStmtCore?`).
  let rhsCore ←
    match (match Expr.abiTyWithEnv? env target with
          | some (Ty.array elemTy _) => some elemTy
          | _ => none) with
    | some elemTy =>
        match Expr.toCoreAsWithEnv? storageNames env elemTy rhs with
        | some c => some c
        | none => Expr.toCore? storageNames rhs
    | none => Expr.toCore? storageNames rhs
  match indexes with
  | [] =>
      let lastIndex :=
        SolidCore.Solidity.Source.Expr.binary
          SolidCore.Solidity.Source.BinaryOp.sub
          (SolidCore.Solidity.Source.Expr.var name)
          (SolidCore.Solidity.Source.Expr.word 1)
      some
        (SolidCore.Solidity.Source.Stmt.block
          [ SolidCore.Solidity.Source.Stmt.storageArrayPushRef name none
          , SolidCore.Solidity.Source.Stmt.assign
              (SolidCore.Solidity.Source.LValue.index
                (SolidCore.Solidity.Source.LValue.var name)
                lastIndex)
              rhsCore ])
  | _ =>
      some
        (SolidCore.Solidity.Source.Stmt.storageArrayPushRefPathAssign
          name indexes rhsCore)

/-- NARROW-PUSH (#183): env-aware sibling of `storageArrayPushPathCore?` for a
    STATE-VARIABLE storage array (`arr.push(a + c)`, `arr2d[0].push(a + c)`).
    The pushed value is lowered against the array ELEMENT type via
    `toCoreAsWithEnv?`, so a narrow (`uintN`/`intN`) checked-arithmetic argument
    keeps its operand-width `uintCleanup`/`intCleanup` (→ Panic 0x11 on
    overflow) instead of the env-less `toCore?` that ran it at 256 bits and
    silently wrapped. A genuine explicit truncating cast (`arr.push(uint8(w))`)
    is not peeled by `toCoreAsWithEnv?` and still truncates. -/
def storageArrayPushPathCoreWithEnv? (env : TypeEnv) (storageNames : List Name)
    (target : Expr) (value : Expr) : Option CoreStmt :=
  match target with
  -- TERNARY-PUSH-TARGET (env-aware sibling): branch a ternary-selected push
  -- target into an `ifElse`, lowering the pushed value against EACH branch's
  -- own element type (see `storageArrayPushPathCore?`). Only the taken branch
  -- runs, so the value is evaluated once.
  | Expr.ternary cond thenTarget elseTarget => do
      let condCore ← Expr.toCore? storageNames cond
      let thenStmt ←
        storageArrayPushPathCoreWithEnv? env storageNames thenTarget value
      let elseStmt ←
        storageArrayPushPathCoreWithEnv? env storageNames elseTarget value
      some (SolidCore.Solidity.Source.Stmt.ifElse condCore thenStmt elseStmt)
  | _ => do
    let (name, indexes) ←
      Expr.storagePathCoreWithEnv? storageNames env target
    let valueCore ←
      match (match Expr.abiTyWithEnv? env target with
            | some (Ty.array elemTy _) => some elemTy
            | _ => none) with
      | some elemTy =>
          match Expr.toCoreAsWithEnv? storageNames env elemTy value with
          | some c => some c
          | none => Expr.toCore? storageNames value
      | none => Expr.toCore? storageNames value
    match indexes with
    | [] =>
        some (SolidCore.Solidity.Source.Stmt.storageArrayPush name (some valueCore))
    | _ =>
        some
          (SolidCore.Solidity.Source.Stmt.storageArrayPushPath
            name indexes (some valueCore))

/-- Env-aware zero-argument sibling for a ternary-selected storage-array
    receiver. The condition is evaluated before the selected `push()`, at its
    inferred source width, matching Solidity's conditional-expression
    semantics. Ordinary storage paths keep the same push core as the env-less
    lowering. -/
def storageArrayEmptyPushPathCoreWithEnv? (env : TypeEnv)
    (storageNames : List Name) (target : Expr) : Option CoreStmt :=
  match target with
  | Expr.ternary cond thenTarget elseTarget => do
      let condCore ← Expr.toCoreAsWithEnv? storageNames env Ty.bool cond
      let thenStmt ←
        storageArrayEmptyPushPathCoreWithEnv? env storageNames thenTarget
      let elseStmt ←
        storageArrayEmptyPushPathCoreWithEnv? env storageNames elseTarget
      some (SolidCore.Solidity.Source.Stmt.ifElse condCore thenStmt elseStmt)
  | _ => do
      let (name, indexes) ←
        Expr.storagePathCoreWithEnv? storageNames env target
      match indexes with
      | [] =>
          some (SolidCore.Solidity.Source.Stmt.storageArrayPush name none)
      | _ =>
          some
            (SolidCore.Solidity.Source.Stmt.storageArrayPushPath
              name indexes none)

def Expr.noReturnEffectStmtCoreWithStorageRefs?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (expr : Expr) : Option CoreStmt :=
  -- NARROW-PUSH (#183): intercept a state-variable array push with a value
  -- argument and lower the value env-aware (element-width checked cleanup)
  -- before the env-less `noReturnEffectStmtCore?` would drop it. Any shape the
  -- env-aware helper cannot lower (`none`) falls through to the prior paths.
  match expr with
  | Expr.call (Expr.member target "push") [] =>
      match storageArrayEmptyPushPathCoreWithEnv? env storageNames target with
      | some coreStmt => some coreStmt
      | none =>
          match Expr.noReturnEffectStmtCore? storageNames expr with
          | some coreStmt => some coreStmt
          | none =>
              Expr.storageRefArrayMemberStmtCore?
                storageRefEnv env storageNames expr
  | Expr.call (Expr.member target "push") [Arg.positional value] =>
      match storageArrayPushPathCoreWithEnv? env storageNames target value with
      | some coreStmt => some coreStmt
      | none =>
          match Expr.noReturnEffectStmtCore? storageNames expr with
          | some coreStmt => some coreStmt
          | none =>
              Expr.storageRefArrayMemberStmtCore?
                storageRefEnv env storageNames expr
  | _ =>
      match Expr.noReturnEffectStmtCore? storageNames expr with
      | some coreStmt => some coreStmt
      | none =>
          Expr.storageRefArrayMemberStmtCore?
            storageRefEnv env storageNames expr

def storageAliasDeclFromRefCore? (storageRefEnv : StorageRefEnv)
    (binding : VarBinding) (source : Name) : Option CoreStmt :=
  match binding.name, binding.location with
  | some name, some DataLocation.storage =>
      if StorageRefEnv.isStorageRef storageRefEnv source then
        some (SolidCore.Solidity.Source.Stmt.storageAliasFrom name source)
      else
        none
  | _, _ => none

def storageAliasDeclFromRefPathCore? (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name) (binding : VarBinding)
    (source : Expr) : Option CoreStmt := do
  let name ← binding.name
  match binding.location with
  | some DataLocation.storage =>
      let (target, indexes) ←
        Expr.storageRefPathCoreWithEnv? storageRefEnv storageNames env source
      match indexes with
      | [] =>
          some (SolidCore.Solidity.Source.Stmt.storageAliasFrom name target)
      | _ =>
          some
            (SolidCore.Solidity.Source.Stmt.storageAliasFromPath
              name target indexes)
  | _ => none

/-- G#116: lower a `T storage p = cond ? thenBranch : elseBranch;` local. solc
    accepts a storage-pointer initialized from a conditional of two storage
    references (the conditional is itself a storage reference). At runtime the
    pointer must ALIAS the SELECTED branch, so lower to an `ifElse` that runs the
    matching storage-alias DECL in the CURRENT scope (the `ifElse` evaluator runs
    the chosen bare branch directly — no scope push — so `p` persists). -/
def storageAliasDeclFromTernaryCore? (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name) (binding : VarBinding)
    (cond thenExpr elseExpr : Expr) : Option CoreStmt := do
  let name ← binding.name
  match binding.location with
  | some DataLocation.storage =>
      let condCore ← Expr.conditionCoreWithEnv? storageNames env cond
      let thenStmt ←
        Expr.storageRefBranchAliasDeclCore? storageRefEnv storageNames
          name thenExpr
      let elseStmt ←
        Expr.storageRefBranchAliasDeclCore? storageRefEnv storageNames
          name elseExpr
      some
        (SolidCore.Solidity.Source.Stmt.ifElse condCore thenStmt elseStmt)
  | _ => none

def storageAliasAssignmentCore? (storageRefEnv : StorageRefEnv)
    (storageNames : List Name) (name target : Name) : Option CoreStmt :=
  if StorageRefEnv.isStorageRef storageRefEnv name then
    match stateNameRuntimeKey? target storageNames with
    | some key =>
      some (SolidCore.Solidity.Source.Stmt.storageAliasAssign name key)
    | none =>
    if StorageRefEnv.isStorageRef storageRefEnv target then
      some (SolidCore.Solidity.Source.Stmt.storageAliasAssignFrom name target)
    else
      none
  else
    none

/-- R3 (#188): re-point a storage-alias local `name` to ANY storage-reference
    RHS shape — the ASSIGN counterpart of the decl dispatch
    (`Expr.storageRefBranchAliasDeclCore?`). This is what a storage-pointer
    RETURN lowers to after `Parameters.returnAssignmentStmtsFromExpr?`
    (`retN = arr[i]` / `m[k]` / `o.inner` — struct members are index ordinals
    after `resolveStructs`), so an INDEXED/MEMBER path must emit the existing
    `storageAliasAssignPath`/`storageAliasAssignFromPath` re-points instead of
    falling through to a VALUE load. A bare-ident RHS keeps the exact
    `storageAliasAssignmentCore?` behaviour. -/
def storageAliasAssignmentExprCore? (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name) (name : Name) :
    Expr -> Option CoreStmt
  | Expr.ident target =>
      storageAliasAssignmentCore? storageRefEnv storageNames name target
  | Expr.ternary cond thenExpr elseExpr =>
      -- G#116 (assign counterpart): re-pointing a storage-pointer local from a
      -- conditional of two storage references (`p = cond ? y : x`) must RE-POINT
      -- `p` to the SELECTED branch, exactly like the decl-from-ternary form
      -- (`storageAliasDeclFromTernaryCore?`). Branch into an `ifElse` that runs
      -- the matching re-point ASSIGN in the CURRENT scope (the `ifElse` evaluator
      -- runs the chosen bare branch directly — no scope push — so the re-point
      -- persists). Recurses so either branch may itself be a path or nested
      -- ternary. Without this arm the ternary RHS fell through to generic
      -- lowering, which left `p` aliasing its original decl target.
      if StorageRefEnv.isStorageRef storageRefEnv name then do
        let condCore ← Expr.conditionCoreWithEnv? storageNames env cond
        let thenStmt ←
          storageAliasAssignmentExprCore? storageRefEnv env storageNames name thenExpr
        let elseStmt ←
          storageAliasAssignmentExprCore? storageRefEnv env storageNames name elseExpr
        some (SolidCore.Solidity.Source.Stmt.ifElse condCore thenStmt elseStmt)
      else
        none
  | rhs =>
      if StorageRefEnv.isStorageRef storageRefEnv name then
        match Expr.storageRefPathCoreWithEnv? storageRefEnv storageNames env rhs with
        | some (source, indexes) =>
            match indexes with
            | [] =>
                some
                  (SolidCore.Solidity.Source.Stmt.storageAliasAssignFrom
                    name source)
            | _ =>
                some
                  (SolidCore.Solidity.Source.Stmt.storageAliasAssignFromPath
                    name source indexes)
        | none => do
            let (target, indexes) ←
              Expr.storagePathCoreWithEnv? storageNames env rhs
            match indexes with
            | [] =>
                some
                  (SolidCore.Solidity.Source.Stmt.storageAliasAssign
                    name target)
            | _ =>
                some
                  (SolidCore.Solidity.Source.Stmt.storageAliasAssignPath
                    name target indexes)
      else
        none

/-- CHAINED storage-pointer assignment `q = p = y` (right-associative): the
    VALUE of the inner `p = y` is the storage reference now held by `p`, so the
    outer `q = (that)` re-points `q` to the SAME target. Desugar a chain of
    storage-pointer rebinds into the SEQUENCE of individual re-points, spliced
    into the enclosing statement list (NOT a block — that would push a scope and
    drop the re-points). Recurses on the RHS so an arbitrarily deep chain
    (`r = q = p = y`) fully unfolds; the innermost pointer re-points to its own
    RHS shape via `storageAliasAssignmentExprCore?`, and each outer pointer
    re-points to alias the pointer immediately to its right. Returns `none` for
    a non-pointer chain (an ordinary value chain `a = b = 5` keeps its existing
    generic `assignExpr`-nesting lowering). -/
def storageAliasChainedAssignCore? (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name) (name : Name) :
    Expr -> Option (List CoreStmt)
  | Expr.assign (Expr.ident inner) AssignOp.assign innerRhs =>
      if StorageRefEnv.isStorageRef storageRefEnv name
          && StorageRefEnv.isStorageRef storageRefEnv inner then do
        let innerStmts ←
          storageAliasChainedAssignCore? storageRefEnv env storageNames inner innerRhs
        let outer ←
          storageAliasAssignmentCore? storageRefEnv storageNames name inner
        some (innerStmts ++ [outer])
      else
        none
  | rhs =>
      (storageAliasAssignmentExprCore? storageRefEnv env storageNames name rhs).map
        (fun head => [head])

def Expr.localStorageArrayMemberStmtCore?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) :
    Expr -> Option CoreStmt :=
  Expr.storageRefArrayMemberStmtCore? storageRefEnv env storageNames

def Parameter.returnName (fallbackPrefix : String) (index : Nat)
    (param : Parameter) : Name :=
  param.name.getD (fallbackPrefix ++ toString index)

def Parameter.returnAssignmentStmt (fallbackPrefix : String)
    (index : Nat) (param : Parameter) (expr : Expr) : Stmt :=
  Stmt.expr
    (Expr.assign
      (Expr.ident (Parameter.returnName fallbackPrefix index param))
      AssignOp.assign expr)

def Parameters.returnAssignmentStmtsFromItems? (fallbackPrefix : String) :
    Nat -> List Parameter -> List TupleItem -> Option (List Stmt)
  | _, [], [] => some []
  | index, param :: params, TupleItem.value expr :: items => do
      let tail ←
        Parameters.returnAssignmentStmtsFromItems?
          fallbackPrefix (index + 1) params items
      some
        (Parameter.returnAssignmentStmt
          fallbackPrefix index param expr :: tail)
  | _, _, _ => none

def Parameters.returnAssignmentStmtsFromExpr? (fallbackPrefix : String)
    (params : List Parameter) (expr : Expr) : Option (List Stmt) :=
  if Parameters.hasStorageRef params then
    match params with
    | [param] =>
        some [Parameter.returnAssignmentStmt fallbackPrefix 0 param expr]
    | _ =>
        match expr with
        | Expr.tuple items =>
            Parameters.returnAssignmentStmtsFromItems?
              fallbackPrefix 0 params items
        | _ => none
  else
    none

def Stmt.rewriteStorageReturnAssignmentsFuel (fuel : Nat)
    (fallbackPrefix : String) (returns : List Parameter) :
    Stmt -> Stmt :=
  match fuel with
  | 0 => fun stmt => stmt
  | fuel + 1 => fun
    | stmt@(Stmt.returnValues (some expr)) =>
        match
          Parameters.returnAssignmentStmtsFromExpr?
            fallbackPrefix returns expr
        with
        | some assigns =>
            Stmt.block (assigns ++ [Stmt.returnValues none])
        | none => stmt
    | Stmt.block body =>
        Stmt.block
          (body.map
            (Stmt.rewriteStorageReturnAssignmentsFuel
              fuel fallbackPrefix returns))
    | Stmt.ifElse cond thenBranch elseBranch =>
        Stmt.ifElse cond
          (Stmt.rewriteStorageReturnAssignmentsFuel
            fuel fallbackPrefix returns thenBranch)
          (elseBranch.map
            (Stmt.rewriteStorageReturnAssignmentsFuel
              fuel fallbackPrefix returns))
    | Stmt.whileLoop cond body =>
        Stmt.whileLoop cond
          (Stmt.rewriteStorageReturnAssignmentsFuel
            fuel fallbackPrefix returns body)
    | Stmt.doWhile body cond =>
        Stmt.doWhile
          (Stmt.rewriteStorageReturnAssignmentsFuel
            fuel fallbackPrefix returns body)
          cond
    | Stmt.forLoop init cond post body =>
        Stmt.forLoop
          (init.map
            (Stmt.rewriteStorageReturnAssignmentsFuel
              fuel fallbackPrefix returns))
          cond post
          (Stmt.rewriteStorageReturnAssignmentsFuel
            fuel fallbackPrefix returns body)
    | Stmt.tryCatch expr clauses =>
        Stmt.tryCatch expr
          (clauses.map
            (fun
              | CatchClause.clause name params body =>
                  CatchClause.clause name params
                    (Stmt.rewriteStorageReturnAssignmentsFuel
                      fuel fallbackPrefix returns body)))
    | Stmt.tryCatchReturns expr params success clauses =>
        Stmt.tryCatchReturns expr params
          (Stmt.rewriteStorageReturnAssignmentsFuel
            fuel fallbackPrefix returns success)
          (clauses.map
            (fun
              | CatchClause.clause name catchParams body =>
                  CatchClause.clause name catchParams
                    (Stmt.rewriteStorageReturnAssignmentsFuel
                      fuel fallbackPrefix returns body)))
    | Stmt.unchecked body =>
        Stmt.unchecked
          (Stmt.rewriteStorageReturnAssignmentsFuel
            fuel fallbackPrefix returns body)
    | stmt => stmt
termination_by fuel

/-- Storage-pointer return rewriting only traverses source syntax, but still uses
    fuel to make the transform's structural decrease explicit to Lean.  Keep
    this in line with the other whole-source transforms: 32 exposed a semantic
    cutoff at 31 nested statement nodes in otherwise valid Solidity. -/
def defaultStorageReturnRewriteFuel : Nat := 1024

def Stmt.rewriteStorageReturnAssignments (fallbackPrefix : String)
    (returns : List Parameter) (stmt : Stmt) : Stmt :=
  Stmt.rewriteStorageReturnAssignmentsFuel
    defaultStorageReturnRewriteFuel fallbackPrefix returns stmt

/-- Nested-call-argument HOISTING bound (stage E). The historical role of this
    constant — the inline-expansion depth budget of the deleted splice path,
    whose exhaustion silently rejected recursion — is GONE: no callee splices
    and recursion depth is bounded only by the interpreter's statement fuel.
    What remains bounded is the syntactic nesting depth of internal calls
    inside a single expression's argument list (`f(g(h(...)))`), which the
    hoisting machinery peels one level per unit; 64 exceeds any real program
    and the elaboration-cluster termination measure needs a decreasing Nat. -/
def defaultInternalCallInlineFuel : Nat := 64

def Stmt.listLeadingBeforeFinalTopLevelModifierPlaceholder? :
    List Stmt -> Option (List Stmt)
  | [] => none
  | Stmt.modifierPlaceholder :: [] => some []
  | Stmt.modifierPlaceholder :: _ :: _ => none
  | stmt :: rest => do
      let before ← Stmt.listLeadingBeforeFinalTopLevelModifierPlaceholder? rest
      some (stmt :: before)

def Stmt.leadingBeforeFinalTopLevelModifierPlaceholder? :
    Stmt -> Option (List Stmt)
  | Stmt.modifierPlaceholder => some []
  | Stmt.block body =>
      Stmt.listLeadingBeforeFinalTopLevelModifierPlaceholder? body
  | _ => none

def modifierApplyLeadingSource? (decl : SourceModifierDecl)
    (invocation : SourceModifierInvocation) (inner : Stmt) :
    Option Stmt := do
  let body ← decl.body
  let body := ModifierDecl.aliasParamsInBody decl body
  let before ← Stmt.leadingBeforeFinalTopLevelModifierPlaceholder? body
  let prefixStmts ← modifierParamBindingsWithArgs? decl invocation.args
  some (Stmt.block (prefixStmts ++ before ++ [inner]))

def functionExpandLeadingModifiers? (available : List SourceModifierDecl) :
    List SourceModifierInvocation -> Stmt -> Option Stmt
  | [], body => some body
  | invocation :: rest, body => do
      let inner ← functionExpandLeadingModifiers? available rest body
      let modifierDecl ← modifierResolve? available invocation.target
      modifierApplyLeadingSource? modifierDecl invocation inner

def Ty.internalCallConversionCore? (targetTy : Ty) :
    Option (CoreExpr -> CoreExpr) :=
  match targetTy with
  | Ty.bool => some id
  | Ty.address _ => some id
  | Ty.uint bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 then
        some (fun expr => SolidCore.Solidity.Source.Expr.uintCast bits expr)
      else
        none
  | Ty.int bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 then
        some (fun expr => SolidCore.Solidity.Source.Expr.intCast bits expr)
      else
        none
  | _ => none

def Expr.internalSingleReturnCallConversion? :
    Expr -> Option (Name × List Arg × (CoreExpr -> CoreExpr))
  | Expr.call (Expr.ident name) args => some (name, args, id)
  | Expr.call (Expr.member (Expr.typeName (Ty.user path)) method) args => do
      let libraryName ← pathLast? path
      some ("__library_" ++ libraryName ++ "_" ++ method, args, id)
  | Expr.call (Expr.typeName targetTy) [Arg.positional inner] => do
      let (name, args, innerConvert) ←
        Expr.internalSingleReturnCallConversion? inner
      let convert ← Ty.internalCallConversionCore? targetTy
      some (name, args, fun retExpr => convert (innerConvert retExpr))
  | _ => none
termination_by expr => sizeOf expr

def Arg.internalSingleReturnCallExpr? : Arg -> Option Expr
  | Arg.positional expr => do
      let _ ← Expr.internalSingleReturnCallConversion? expr
      some expr
  | Arg.named _ expr => do
      let _ ← Expr.internalSingleReturnCallConversion? expr
      some expr

def Args.replaceInternalSingleReturnCallExprArg? (fallbackPrefix : String) :
    Nat -> List Arg -> Option (Nat × Expr × Name × List Arg)
  | _, [] => none
  | index, arg :: rest =>
      let tempName := internalCallArgTempName fallbackPrefix index
      match Arg.internalSingleReturnCallExpr? arg with
      | some expr =>
          some
            ( index
            , expr
            , tempName
            , Arg.withExpr (Expr.ident tempName) arg :: rest )
      | none => do
          let (foundIndex, expr, foundTemp, rest') ←
            Args.replaceInternalSingleReturnCallExprArg?
              fallbackPrefix (index + 1) rest
          some (foundIndex, expr, foundTemp, arg :: rest')

def Expr.actualInternalSingleReturnCall?
    (functions : List FunctionDecl) (env : TypeEnv) (expr : Expr) :
    Option (Expr × Ty) :=
  let pointerCall? : Option (Expr × Ty) :=
    match expr with
    -- A member call may be an error constructor, a direct library/contract
    -- call, or another declaration form that merely has a function-shaped
    -- type. It is not a run-time internal-function pointer and must remain on
    -- its dedicated lowering path so qualified custom-error overload
    -- resolution survives. Pointer calls covered here have bare or computed
    -- callees (`storedFn(a)`, `localFn(a)`, `g()(a)`).
    | Expr.call (Expr.member _ _) _ => none
    | Expr.call callee _ =>
        match Expr.abiTyWithInternalFunctionsEnv? functions [] env callee with
        | some (Ty.functionWithLocations _ _ [returnTy] [_] _
            Visibility.internal_) =>
            some (expr, returnTy)
        | some (Ty.functionWithLocations _ _ [returnTy] [_] _
            Visibility.private_) =>
            some (expr, returnTy)
        | _ => none
    | _ => none
  match Expr.internalSingleReturnCallConversion? expr with
  | some (name, args, _) =>
      match FunctionDecl.findInternalCalleeWithArgs?
          functions env name args with
      | some (callee, _) =>
          match callee.returns with
          | [ret] => some (expr, ret.ty)
          | _ => none
      -- A bare identifier may name an internal function-pointer local,
      -- parameter, or state variable rather than a declared function.  It has
      -- the same syntactic conversion shape as a direct call, so the old `do`
      -- arm returned `none` before reaching the pointer fallback below.  Keep
      -- direct declarations authoritative, then classify the unresolved call
      -- from the identifier's function type.
      | none => pointerCall?
  | none =>
      -- An arbitrary-callee call can still be an internal single-return call:
      -- `g()(7)` dispatches through the internal function pointer returned by
      -- `g`. Treat it like a named internal call for argument-position ANF
      -- hoisting so it can appear inside `abi.encode`, another call's argument,
      -- or any other eager expression position.
      pointerCall?

def Arg.actualInternalSingleReturnCall?
    (functions : List FunctionDecl) (env : TypeEnv) :
    Arg -> Option (Expr × Ty)
  | Arg.positional expr => Expr.actualInternalSingleReturnCall?
      functions env expr
  | Arg.named _ expr => Expr.actualInternalSingleReturnCall?
      functions env expr

mutual

def Expr.replaceAbiInternalSingleReturnCall?
    (functions : List FunctionDecl) (env : TypeEnv)
    (fallbackPrefix : String) :
    Nat -> Expr -> Option (Expr × Name × Expr)
  | index, Expr.call (Expr.member (Expr.ident "abi") member) args =>
      if
          member == "encode" || member == "encodePacked" ||
            member == "encodeWithSelector" ||
            member == "encodeWithSignature" then
        match Args.replaceActualInternalSingleReturnCallArg?
            functions env fallbackPrefix index args with
        | some (callExpr, _, tmpName, replacedArgs) =>
            some
              ( callExpr
              , tmpName
              , Expr.call (Expr.member (Expr.ident "abi") member)
                  replacedArgs )
        | none => do
            let (callExpr, tmpName, replacedArgs) ←
              Args.replaceAbiInternalSingleReturnCall?
                functions env fallbackPrefix index args
            some
              ( callExpr
              , tmpName
              , Expr.call (Expr.member (Expr.ident "abi") member)
                  replacedArgs )
      else
        match Args.replaceAbiInternalSingleReturnCall?
            functions env fallbackPrefix index args with
        | some (callExpr, tmpName, replacedArgs) =>
            some
              ( callExpr
              , tmpName
              , Expr.call (Expr.member (Expr.ident "abi") member)
                  replacedArgs )
        | none => none
  | index, Expr.call target args =>
      match Expr.replaceAbiInternalSingleReturnCall?
          functions env fallbackPrefix index target with
      | some (callExpr, tmpName, replacedTarget) =>
          some (callExpr, tmpName, Expr.call replacedTarget args)
      | none => do
          let (callExpr, tmpName, replacedArgs) ←
            Args.replaceAbiInternalSingleReturnCall?
              functions env fallbackPrefix index args
          some (callExpr, tmpName, Expr.call target replacedArgs)
  | index, Expr.callWithOptions target options args =>
      match Expr.replaceAbiInternalSingleReturnCall?
          functions env fallbackPrefix index target with
      | some (callExpr, tmpName, replacedTarget) =>
          some
            (callExpr, tmpName,
              Expr.callWithOptions replacedTarget options args)
      | none => do
          let (callExpr, tmpName, replacedArgs) ←
            Args.replaceAbiInternalSingleReturnCall?
              functions env fallbackPrefix index args
          some
            (callExpr, tmpName,
              Expr.callWithOptions target options replacedArgs)
  | _, _ => none
termination_by _ expr => (sizeOf expr, 0, 0)

def Arg.replaceAbiInternalSingleReturnCall?
    (functions : List FunctionDecl) (env : TypeEnv)
    (fallbackPrefix : String) (index : Nat) :
    Arg -> Option (Expr × Name × Arg)
  | Arg.positional expr => do
      let (callExpr, tmpName, replacedExpr) ←
        Expr.replaceAbiInternalSingleReturnCall?
          functions env fallbackPrefix index expr
      some (callExpr, tmpName, Arg.positional replacedExpr)
  | Arg.named name expr => do
      let (callExpr, tmpName, replacedExpr) ←
        Expr.replaceAbiInternalSingleReturnCall?
          functions env fallbackPrefix index expr
      some (callExpr, tmpName, Arg.named name replacedExpr)
termination_by arg => (sizeOf arg, 0, 1)

def Args.replaceActualInternalSingleReturnCallArg?
    (functions : List FunctionDecl) (env : TypeEnv)
    (fallbackPrefix : String) :
    Nat -> List Arg -> Option (Expr × Ty × Name × List Arg)
  | _, [] => none
  | index, arg :: rest =>
      let tempName := internalCallArgTempName fallbackPrefix index
      match Arg.actualInternalSingleReturnCall? functions env arg with
      | some (expr, retTy) =>
          let tempExpr :=
            Expr.call (Expr.typeName retTy)
              [Arg.positional (Expr.ident tempName)]
          some
            ( expr
            , retTy
            , tempName
            , Arg.withExpr tempExpr arg :: rest )
      | none => do
          let (expr, retTy, foundTemp, rest') ←
            Args.replaceActualInternalSingleReturnCallArg?
              functions env fallbackPrefix (index + 1) rest
          some (expr, retTy, foundTemp, arg :: rest')
termination_by _ args => (sizeOf args, 0, 2)

def Args.replaceAbiInternalSingleReturnCall?
    (functions : List FunctionDecl) (env : TypeEnv)
    (fallbackPrefix : String) :
    Nat -> List Arg -> Option (Expr × Name × List Arg)
  | _, [] => none
  | index, arg :: rest =>
      match Arg.replaceAbiInternalSingleReturnCall?
          functions env fallbackPrefix index arg with
      | some (expr, foundTemp, replacedArg) =>
          some (expr, foundTemp, replacedArg :: rest)
      | none => do
          let (expr, foundTemp, rest') ←
            Args.replaceAbiInternalSingleReturnCall?
              functions env fallbackPrefix (index + 1) rest
          some (expr, foundTemp, arg :: rest')
termination_by _ args => (sizeOf args, 0, 3)

end

/-- Fresh temp name for the RHS of a `base[<internal call>] = rhs` assignment,
    bound (and thus evaluated) *before* the hoisted index call so evaluation
    order matches solc (RHS is evaluated before the LHS index). -/
def indexAssignRhsTempName : Name := "_sol_index_assign_rhs"

-- R2: `Expr.indexReadCoreBuilder?` moved earlier in the file (before the
-- env-aware lowering mutual block, which uses it for narrow index keys).

/-- LValue counterpart of `Expr.indexReadCoreBuilder?`, mirroring the
    `Expr.index` cases of `Expr.toCoreLValue?` (state-var `storageIndex`,
    general `index`). Used to lower the target of `base[<internal call>] = rhs`. -/
def Expr.indexLValueCoreBuilder? (storageNames : List Name) (base : Expr) :
    Option (CoreExpr -> CoreLValue) :=
  match base with
  | Expr.ident name =>
      match stateNameRuntimeKey? name storageNames with
      | some key =>
          some (fun idx => SolidCore.Solidity.Source.LValue.storageIndex key idx)
      | none => do
          let baseCore ← Expr.toCoreLValue? storageNames (Expr.ident name)
          some (fun idx => SolidCore.Solidity.Source.LValue.index baseCore idx)
  | _ => do
      let baseCore ← Expr.toCoreLValue? storageNames base
      some (fun idx => SolidCore.Solidity.Source.LValue.index baseCore idx)

-- CALL-POSITION: does this statement contain a `continue` that binds to the
-- *enclosing* loop (i.e. one not captured by a nested `while`/`for`/`do-while`)?
-- Used to guard the loop-condition call-hoisting desugar: when the condition
-- of a `for`/`do-while` loop contains a call, we rewrite the loop into a
-- `while(1) { … if(cond) …; body; post }` form, and that rewrite only
-- preserves `continue` semantics when the body has no bare `continue` (a bare
-- `continue` in the desugared form would skip the condition re-check / `post`
-- step). Nested loops capture their own `continue`, so we do NOT descend into
-- them. `try`/`tryCatchReturns` are treated conservatively as "may contain"
-- — returning `true` only *disables* the new acceptance (falling back to the
-- prior behaviour), so it can never produce wrong output.
mutual
def Stmt.mentionsBareContinue : Stmt -> Bool
  | Stmt.continue => true
  | Stmt.block body => Stmt.listMentionsBareContinue body
  | Stmt.ifElse _ t none => Stmt.mentionsBareContinue t
  | Stmt.ifElse _ t (some e) =>
      Stmt.mentionsBareContinue t || Stmt.mentionsBareContinue e
  | Stmt.unchecked s => Stmt.mentionsBareContinue s
  | Stmt.tryCatch _ _ => true
  | Stmt.tryCatchReturns _ _ _ _ => true
  | _ => false
def Stmt.listMentionsBareContinue : List Stmt -> Bool
  | [] => false
  | s :: rest =>
      Stmt.mentionsBareContinue s || Stmt.listMentionsBareContinue rest
end

/-- CLUSTER-B #7 (extcall-binary): recognise an EXTERNAL/member single-return
    call in a binary operand and report its single declared return type. Only
    high-level typed member calls (`t.f(..)` / `t.f{..}(..)`) with EXACTLY ONE
    declared return are matched; low-level `.call`/`.staticcall`/etc. and
    reserved members are filtered upstream by `toExternalCallWithKindEnv?` and
    have no declared-return entry, so they return `none` here (and the caller
    then preserves the prior over-reject rather than emitting unsound code). -/
def Expr.externalMemberSingleReturnCallTy? (storageNames : List Name)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv) :
    Expr -> Option Ty
  | expr@(Expr.call (Expr.member _ _) _)
  | expr@(Expr.callWithOptions (Expr.member _ _) _ _) =>
      match
          Expr.externalCallDeclaredReturnTysWithKindEnv?
            storageNames env externalCallKindEnv expr with
      | some [ty] => some ty
      | _ => none
  | _ => none

/-- CLUSTER-B #7 (extcall-binary): hoist a single EXTERNAL/member single-return
    call out of a BINARY operand into a prefix `tryExternalCall` statement,
    mirroring exactly the internal-call binary hoister
    (`internalBinarySingleReturnUseCore?`) but using the existing external-call
    lowering (`externalCallSingleReturnCoreWithKindEnv?`). Only handles the case
    where EXACTLY ONE operand is an external member call and the OTHER operand is
    a pure expression (`Expr.toCore?` succeeds); every other shape (both
    external, or the non-call operand containing its own nested call) returns
    `none` so the caller falls back to the prior behaviour. solc legacy
    left-to-right order is preserved: the external call is emitted in its source
    position (call-on-the-left → hoisted first; call-on-the-right → the pure lhs
    is evaluated into a temp first, then the call). For `&&`/`||` with the call
    on the RIGHT the short-circuit is materialised as an `ifElse` on the lhs
    temp so the (effectful) external call is skipped exactly when solc skips it;
    with the call on the LEFT the pure rhs has no observable effect, so a plain
    `binary` reproduces the result without a branch (matching the internal
    hoister's call-on-the-left arm). -/
def externalBinarySingleReturnUseCore?
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (functions freeFunctions : List FunctionDecl)
    (op : BinaryOp) (lhs rhs : Expr) (useResult : CoreExpr -> CoreStmt) :
    Option CoreStmt :=
  let lhsExt? :=
    Expr.externalMemberSingleReturnCallTy? storageNames env externalCallKindEnv lhs
  let rhsExt? :=
    Expr.externalMemberSingleReturnCallTy? storageNames env externalCallKindEnv rhs
  match lhsExt?, rhsExt? with
  | some lhsTy, none => do
      -- External call on the LEFT, pure operand on the RIGHT. Ordinary
      -- operators: solc evaluates the RIGHT operand FIRST
      -- (ExpressionCompiler.cpp:614-615), so park the RHS value in a temp
      -- before performing the external call. Short-circuit ops keep the
      -- left-first shape (the runtime boolAnd/boolOr arm guards the pure RHS).
      let coreOp ← BinaryOp.toCore? op
      let rhsCore ← Expr.toCore? storageNames rhs
      match op with
      | BinaryOp.boolAnd | BinaryOp.boolOr =>
          Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
            storageNames env externalCallKindEnv lhsTy lhs
            (fun retExpr =>
              useResult
                (SolidCore.Solidity.Source.Expr.binary coreOp retExpr rhsCore))
      | _ =>
          match
              Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env rhs with
          | some rhsTy => do
              let rhsCoreTy ← Ty.toCore? rhsTy
              let rhsTmp := "_sol_bin_ext_rhs"
              let callCore ←
                Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv lhsTy lhs
                  (fun retExpr =>
                    useResult
                      (SolidCore.Solidity.Source.Expr.binary coreOp retExpr
                        (SolidCore.Solidity.Source.Expr.var rhsTmp)))
              some
                (SolidCore.Solidity.Source.Stmt.block
                  [ SolidCore.Solidity.Source.Stmt.varDecl
                      rhsCoreTy rhsTmp (some rhsCore)
                  , callCore ])
          | none =>
              -- RHS type unresolvable: keep the previous (left-call-first)
              -- shape rather than decline.
              Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                storageNames env externalCallKindEnv lhsTy lhs
                (fun retExpr =>
                  useResult
                    (SolidCore.Solidity.Source.Expr.binary coreOp
                      retExpr rhsCore))
  | none, some rhsTy => do
      -- Pure operand on the LEFT, external call on the RIGHT. Ordinary
      -- operators: solc evaluates the RIGHT (external call) FIRST
      -- (ExpressionCompiler.cpp:614-615); the pure LEFT operand stays in the
      -- residual binary, whose runtime arm is right-then-left. Short-circuit
      -- ops evaluate the LEFT into a temp and guard the RIGHT call.
      let coreOp ← BinaryOp.toCore? op
      let lhsCore ← Expr.toCore? storageNames lhs
      match op with
      | BinaryOp.boolAnd | BinaryOp.boolOr => do
          let lhsTy ←
            Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env lhs
          let lhsCoreTy ← Ty.toCore? lhsTy
          let lhsTmp := "_sol_bin_ext_lhs"
          let rhsCallCore ←
            Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
              storageNames env externalCallKindEnv rhsTy rhs
              (fun retExpr =>
                useResult
                  (SolidCore.Solidity.Source.Expr.binary coreOp
                    (SolidCore.Solidity.Source.Expr.var lhsTmp) retExpr))
          let branchCore :=
            match op with
            | BinaryOp.boolAnd =>
                SolidCore.Solidity.Source.Stmt.ifElse
                  (SolidCore.Solidity.Source.Expr.var lhsTmp)
                  rhsCallCore
                  (useResult (SolidCore.Solidity.Source.Expr.word 0))
            | _ =>
                SolidCore.Solidity.Source.Stmt.ifElse
                  (SolidCore.Solidity.Source.Expr.var lhsTmp)
                  (useResult (SolidCore.Solidity.Source.Expr.word 1))
                  rhsCallCore
          some
            (SolidCore.Solidity.Source.Stmt.block
              [ SolidCore.Solidity.Source.Stmt.varDecl
                  lhsCoreTy lhsTmp (some lhsCore)
              , branchCore ])
      | _ =>
          Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
            storageNames env externalCallKindEnv rhsTy rhs
            (fun retExpr =>
              useResult
                (SolidCore.Solidity.Source.Expr.binary coreOp
                  lhsCore retExpr))
  | some lhsTy, some rhsTy => do
      -- #131 SHORTCIRCUIT-CALL-POS: BOTH operands external single-return calls.
      -- Only the short-circuiting `&&`/`||` are handled (the #131 scope): evaluate
      -- the LEFT call into a bool temp, then guard the RIGHT external call on that
      -- temp so the (effectful) right call runs exactly when solc would evaluate
      -- it. Mirrors the both-internal path 13243-13278. `_ => none` for every
      -- other operator preserves the prior over-reject (no unsound eager both-call
      -- arithmetic).
      let coreOp ← BinaryOp.toCore? op
      match op with
      | BinaryOp.boolAnd
      | BinaryOp.boolOr => do
          let lhsTmp := "_sol_bin_ext_both_lhs"
          let rhsCallCore ←
            Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
              storageNames env externalCallKindEnv rhsTy rhs
              (fun retExpr =>
                useResult
                  (SolidCore.Solidity.Source.Expr.binary coreOp
                    (SolidCore.Solidity.Source.Expr.var lhsTmp) retExpr))
          let skipCore :=
            match op with
            | BinaryOp.boolAnd =>
                useResult (SolidCore.Solidity.Source.Expr.word 0)
            | _ =>
                useResult (SolidCore.Solidity.Source.Expr.word 1)
          let branchCore :=
            match op with
            | BinaryOp.boolAnd =>
                SolidCore.Solidity.Source.Stmt.ifElse
                  (SolidCore.Solidity.Source.Expr.var lhsTmp)
                  rhsCallCore skipCore
            | _ =>
                SolidCore.Solidity.Source.Stmt.ifElse
                  (SolidCore.Solidity.Source.Expr.var lhsTmp)
                  skipCore rhsCallCore
          Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
            storageNames env externalCallKindEnv lhsTy lhs
            (fun retExpr =>
              SolidCore.Solidity.Source.Stmt.block
                [ SolidCore.Solidity.Source.Stmt.varDecl
                    SolidCore.Solidity.Source.Ty.bool lhsTmp (some retExpr)
                , branchCore ])
      | _ => none
  | none, none => none

/- CALL-POSITION CONSOLIDATED (#147-#151): find the leftmost — in evaluation
    order — STRICT-inner internal single-return call inside `expr` (a call that
    is not the whole expression and whose own arguments contain no further such
    call), replace it with `Expr.ident tmp`, and return
    `(that call expression, its return type, the rewritten expression)`.

    Value-returning calls in argument-like positions — array/tuple/struct
    elements (`[g(), h()]`, `S(g(), h())`), `new`/constructor and function-call
    arguments (`new T(g())`, `h(g() + 1)`, `h(a[g()])`) — are represented as
    STATEMENTS in the Executable core, so a call nested there must be hoisted
    into a prefix temp before the surrounding construct is lowered. The direct
    call-position machinery only reaches a bare `f(...)` argument; this walker is
    the generic fallback that peels ONE such nested call so the enclosing
    statement lowering can re-run on the (structurally smaller) rewritten form.

    Short-circuit (`&&`/`||`) right operands and ternary branches are NOT
    descended into, so a conditionally-evaluated call is never hoisted (which
    would change solc's evaluation semantics and could run a call solc skips);
    those positions preserve the prior over-reject. `atRoot` suppresses matching
    the whole expression, so only strictly-nested calls are peeled — a payload
    that is itself a call is left to the existing call-statement arms. -/

/-- R1 / named-argument call order: reorder an INTERNAL call's NAMED arguments
    into the callee's parameter-declaration order (as positional args) so the
    sibling-prefix hoister (`findArgPosInnerCall?`) and the ANF fallback lift
    their nested calls in solc's evaluation order. solc 0.8.35 legacy codegen
    (`ExpressionCompiler.cpp`) reorders named arguments to parameter order and
    THEN evaluates the argument list left-to-right, so `g({b: t(1), a: t(2)})`
    runs the `a` expression `t(2)` first. Both hoisters otherwise lift arguments
    in WRITTEN order, mis-ordering the side-effecting nested calls (argument
    BINDING is already correct — it is reordered by the downstream `orderedArgs?`;
    only the hoist-temp evaluation order was wrong).

    Positional calls short-circuit unchanged, and only a callee that resolves to a
    UNIQUE internal function is reordered — struct construction, external/library
    calls, and event/error/`require`-error argument lists are reordered on their
    own paths and keep their existing (byte-identical) lowering. -/
def Expr.reorderNamedInternalCallArgs
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (callee : Expr) (args : List Arg) : List Arg :=
  if Args.allPositional args then
    args
  else
    match callee with
    | Expr.ident name =>
        match FunctionDecl.findInternalCalleeWithArgs? functions env name args with
        | some (_, ordered) => ordered.map Arg.positional
        | none =>
            match FunctionDecl.findInternalCalleeWithArgs? freeFunctions env name args with
            | some (_, ordered) => ordered.map Arg.positional
            | none => args
    | _ => args

mutual

def Expr.findArgPosInnerCall? (functions : List FunctionDecl)
    (env : TypeEnv) (tmp : Name) (atRoot : Bool) :
    Nat -> Expr -> Option (Expr × Ty × Expr)
  | 0, _ => none
  | fuel + 1, e =>
    let rootCandidate : Option (Expr × Ty × Expr) :=
      if atRoot then none
      else
        match Expr.actualInternalSingleReturnCall? functions env e with
        | some (_, retTy) =>
            -- Replace the hoisted call with the temp read wrapped in an explicit
            -- (value-identity) conversion to the call's own return type, so the
            -- residual expression still carries a type at this position. Bare
            -- idents defeat the env-less array/`new`-argument common-type
            -- inference the re-lowering runs, whereas a `(retTy)(tmp)` node types
            -- exactly as the call result did (matching solc's coercion of the
            -- call's value into the surrounding construct).
            some (e, retTy,
              Expr.call (Expr.typeName retTy) [Arg.positional (Expr.ident tmp)])
        | none => none
    match e with
    | Expr.binary op l r =>
        match op with
        | BinaryOp.boolAnd
        | BinaryOp.boolOr =>
            match Expr.findArgPosInnerCall? functions env tmp false fuel l with
            | some (c, t, l') => some (c, t, Expr.binary op l' r)
            | none => none
        | _ =>
            match Expr.findArgPosInnerCall? functions env tmp false fuel l with
            | some (c, t, l') => some (c, t, Expr.binary op l' r)
            | none =>
                match Expr.findArgPosInnerCall? functions env tmp false fuel r with
                | some (c, t, r') => some (c, t, Expr.binary op l r')
                | none => none
    | Expr.unary op x =>
        match Expr.findArgPosInnerCall? functions env tmp false fuel x with
        | some (c, t, x') => some (c, t, Expr.unary op x')
        | none => none
    | Expr.payableConversion x =>
        match Expr.findArgPosInnerCall? functions env tmp false fuel x with
        | some (c, t, x') => some (c, t, Expr.payableConversion x')
        | none => none
    | Expr.enumFromUInt w x =>
        -- A value-returning call inside an enum conversion (`E(f())`,
        -- `E(uint8(f()))`) is an argument-like position exactly like a unary
        -- operand; descend into the converted expression so the call is peeled
        -- into a sibling temp instead of surviving inside the Core
        -- `enumFromUInt` (where evaluating it as a pure sub-expression is
        -- unsupported and yields a spurious Panic 0).
        match Expr.findArgPosInnerCall? functions env tmp false fuel x with
        | some (c, t, x') => some (c, t, Expr.enumFromUInt w x')
        | none => none
    | Expr.index b i =>
        match Expr.findArgPosInnerCall? functions env tmp false fuel b with
        | some (c, t, b') => some (c, t, Expr.index b' i)
        | none =>
            match Expr.findArgPosInnerCall? functions env tmp false fuel i with
            | some (c, t, i') => some (c, t, Expr.index b i')
            | none => none
    | Expr.member b m =>
        match Expr.findArgPosInnerCall? functions env tmp false fuel b with
        | some (c, t, b') => some (c, t, Expr.member b' m)
        | none => none
    | Expr.slice b s e =>
        -- A value-returning call in a calldata-slice BOUND (`d[1 : f()]`,
        -- `d[g() : h()]`) is an argument-like position exactly like an index
        -- key; descend base, then start, then stop (source L2R) so the call is
        -- peeled into a sibling temp instead of surviving in the Core slice
        -- bound (where it evaluates to a spurious Panic 0).
        match Expr.findArgPosInnerCall? functions env tmp false fuel b with
        | some (c, t, b') => some (c, t, Expr.slice b' s e)
        | none =>
            match s with
            | some sExpr =>
                match Expr.findArgPosInnerCall? functions env tmp false fuel sExpr with
                | some (c, t, s') => some (c, t, Expr.slice b (some s') e)
                | none =>
                    match e with
                    | some eExpr =>
                        match Expr.findArgPosInnerCall? functions env tmp false fuel eExpr with
                        | some (c, t, e') => some (c, t, Expr.slice b s (some e'))
                        | none => none
                    | none => none
            | none =>
                match e with
                | some eExpr =>
                    match Expr.findArgPosInnerCall? functions env tmp false fuel eExpr with
                    | some (c, t, e') => some (c, t, Expr.slice b s (some e'))
                    | none => none
                | none => none
    | Expr.array elems =>
        match Expr.findArgPosInnerCallExprs? functions env tmp fuel elems with
        | some (c, t, elems') => some (c, t, Expr.array elems')
        | none => none
    | Expr.tuple items =>
        match Expr.findArgPosInnerCallTuple? functions env tmp fuel items with
        | some (c, t, items') => some (c, t, Expr.tuple items')
        | none => none
    | Expr.newExpr ty args =>
        match Expr.findArgPosInnerCallArgs? functions env tmp fuel args with
        | some (c, t, args') => some (c, t, Expr.newExpr ty args')
        | none => none
    | Expr.call callee args =>
        let args := Expr.reorderNamedInternalCallArgs functions [] env callee args
        let normal :=
          match Expr.findArgPosInnerCallArgs? functions env tmp fuel args with
          | some (c, t, args') => some (c, t, Expr.call callee args')
          | none =>
              match
                  Expr.findArgPosInnerCall? functions env tmp false fuel callee
              with
              | some (c, t, callee') => some (c, t, Expr.call callee' args)
              | none => rootCandidate
        -- Legacy addmod/mulmod evaluate their three positional arguments from
        -- right to left. Peel the modulus first, then rhs, then lhs, while
        -- keeping every rewritten argument in its original positional slot.
        match callee, args with
        | Expr.ident name, [a, b, m] =>
            if name == "addmod" || name == "mulmod" then
              let mExpr := match m with
                | Arg.positional e | Arg.named _ e => e
              let bExpr := match b with
                | Arg.positional e | Arg.named _ e => e
              let aExpr := match a with
                | Arg.positional e | Arg.named _ e => e
              match
                  Expr.findArgPosInnerCall?
                    functions env tmp false fuel mExpr
              with
              | some (c, t, m') =>
                  some (c, t, Expr.call callee [a, b, Arg.withExpr m' m])
              | none =>
                  match
                      Expr.findArgPosInnerCall?
                        functions env tmp false fuel bExpr
                  with
                  | some (c, t, b') =>
                      some (c, t,
                        Expr.call callee [a, Arg.withExpr b' b, m])
                  | none =>
                      match
                          Expr.findArgPosInnerCall?
                            functions env tmp false fuel aExpr
                      with
                      | some (c, t, a') =>
                          some (c, t,
                            Expr.call callee [Arg.withExpr a' a, b, m])
                      | none => normal
            else
              normal
        | _, _ => normal
    | Expr.callWithOptions callee options args =>
        match Expr.findArgPosInnerCallArgs? functions env tmp fuel args with
        | some (c, t, args') =>
            some (c, t, Expr.callWithOptions callee options args')
        | none => none
    | _ => rootCandidate
termination_by fuel _ => fuel

def Expr.findArgPosInnerCallExprs? (functions : List FunctionDecl)
    (env : TypeEnv) (tmp : Name) :
    Nat -> List Expr -> Option (Expr × Ty × List Expr)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, e :: rest =>
    match Expr.findArgPosInnerCall? functions env tmp false fuel e with
    | some (c, t, e') => some (c, t, e' :: rest)
    | none =>
        match Expr.findArgPosInnerCallExprs? functions env tmp fuel rest with
        | some (c, t, rest') => some (c, t, e :: rest')
        | none => none
termination_by fuel _ => fuel

def Expr.findArgPosInnerCallArgs? (functions : List FunctionDecl)
    (env : TypeEnv) (tmp : Name) :
    Nat -> List Arg -> Option (Expr × Ty × List Arg)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, arg :: rest =>
    let argExpr :=
      match arg with
      | Arg.positional expr => expr
      | Arg.named _ expr => expr
    match Expr.findArgPosInnerCall? functions env tmp false fuel argExpr with
    | some (c, t, e') => some (c, t, Arg.withExpr e' arg :: rest)
    | none =>
        match Expr.findArgPosInnerCallArgs? functions env tmp fuel rest with
        | some (c, t, rest') => some (c, t, arg :: rest')
        | none => none
termination_by fuel _ => fuel

def Expr.findArgPosInnerCallTuple? (functions : List FunctionDecl)
    (env : TypeEnv) (tmp : Name) :
    Nat -> List TupleItem -> Option (Expr × Ty × List TupleItem)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, item :: rest =>
    match item with
    | TupleItem.hole =>
        match Expr.findArgPosInnerCallTuple? functions env tmp fuel rest with
        | some (c, t, rest') => some (c, t, TupleItem.hole :: rest')
        | none => none
    | TupleItem.value expr =>
        match Expr.findArgPosInnerCall? functions env tmp false fuel expr with
        | some (c, t, e') => some (c, t, TupleItem.value e' :: rest)
        | none =>
            match Expr.findArgPosInnerCallTuple? functions env tmp fuel rest with
            | some (c, t, rest') => some (c, t, item :: rest')
            | none => none
termination_by fuel _ => fuel

end

/-! ### General A-normal-form (ANF) call-hoisting pass

    A single, uniform source→source normalization over the surface `Ast` that
    lifts every value-returning internal / library / external single-return call
    that is NESTED inside an arbitrary expression into an ordered sequence of
    temp-local bindings, leaving flat expressions the existing enumerated
    lowering arms already handle. It reproduces solc legacy evaluation order
    (`ExpressionCompiler.cpp`): ordinary function/builtin args left-to-right,
    addmod/mulmod args right-to-left; ordinary binary operands RIGHT-then-LEFT
    (`614-615`); short-circuit `&&`/`||` right operand guarded; ternary branches
    guarded (only the taken branch runs). The
    hoisted result reads a fresh `_sol_hoist_<n>` temp. Because it is wired as a
    body-level FALLBACK that only rewrites statements the enumerated dispatcher
    cannot lower, every currently-lowering (green) statement is left
    byte-identical. -/

/-- Reference-typed hoist temps need an explicit `memory` data location; value
    types take no location. -/
def Ty.anfHoistLocation? : Ty -> Option DataLocation
  | Ty.array _ _ => some DataLocation.memory
  | Ty.bytes => some DataLocation.memory
  | Ty.string => some DataLocation.memory
  | Ty.struct _ _ => some DataLocation.memory
  | Ty.tuple _ => some DataLocation.memory
  -- An unresolved user type is (in practice for a value-returning callee whose
  -- result we hoist) a struct that needs a `memory` location; enums surface as
  -- `Ty.enum`, so this does not mislocate a value-typed enum return.
  | Ty.user _ => some DataLocation.memory
  | _ => none

/-- The fresh-name supply: globally monotone within a function body. The
    `_sol_hoist_` prefix is reserved (verified unused elsewhere). -/
def anfHoistName (n : Nat) : Name := "_sol_hoist_" ++ toString n

/-- Declare a hoist temp with the callee's return type in its UNRESOLVED
    surface form. A callee's return type is RESOLVED (`Ty.struct p fields`) by
    the time it reaches the hoister, but `resolveStructs` — which the produced
    block is re-run through to resolve struct MEMBER accesses on the temp
    (`_sol_hoist_n.field` → ordinal index) — only descends into a member whose
    base type is the unresolved reference `Ty.user p`; an already-resolved
    `Ty.struct` base is treated as done and its members are left unresolved.
    Restoring the surface `Ty.user p` lets the re-run resolve both the type and
    the member. Non-struct types are already in surface form. -/
def Ty.anfTempTy : Ty -> Ty
  | Ty.struct p _ => Ty.user p
  | ty => ty

/-- Oracle: is `e` a value-returning SINGLE-return call with no core `Expr`
    representation (a direct internal call, a library call, or an external
    member call)? If so, its (single) return type — used to declare the hoist
    temp. Deliberately EXCLUDES type-conversion casts `T(inner)` and
    `new`-expressions (those ARE core `Expr`s; their nested call args are hoisted
    by recursing into them), and returns `none` for builtins / events / errors /
    multi-return callees. -/
def Expr.anfHoistableCallTy?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name) :
    Expr -> Option Ty
  | Expr.call (Expr.typeName _) _ => none
  | Expr.newExpr _ _ => none
  | e@(Expr.call (Expr.ident _) _) =>
      match Expr.actualInternalSingleReturnCall? functions env e with
      | some (_, ty) => some ty
      | none =>
          match Expr.actualInternalSingleReturnCall? freeFunctions env e with
          | some (_, ty) => some ty
          | none => none
  | e@(Expr.call (Expr.member _ _) _) =>
      match Expr.actualInternalSingleReturnCall? functions env e with
      | some (_, ty) => some ty
      | none =>
          match Expr.actualInternalSingleReturnCall? freeFunctions env e with
          | some (_, ty) => some ty
          | none =>
              Expr.externalMemberSingleReturnCallTy?
                storageNames env externalCallKindEnv e
  | e@(Expr.callWithOptions (Expr.member _ _) _ _) =>
      Expr.externalMemberSingleReturnCallTy?
        storageNames env externalCallKindEnv e
  | _ => none

/-- R3 (#188): does this hoistable call's single return live in STORAGE? A
    storage-pointer-returning callee's hoist temp must be declared a
    `storage` alias local (`S storage t = refS(i); t.b = 77;` writes
    through the pointer) — a `memory`-located temp would silently write a
    detached copy. -/
def Expr.anfHoistableCallStorageReturn
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (e : Expr) : Bool :=
  let retLocation? : Option (Option DataLocation) := do
    let (name, args, _) ← Expr.internalSingleReturnCallConversion? e
    let (callee, _) ←
      match FunctionDecl.findInternalCalleeWithArgs?
          functions env name args with
      | some found => some found
      | none =>
          FunctionDecl.findInternalCalleeWithArgs?
            freeFunctions env name args
    match callee.returns with
    | [ret] => some ret.location
    | _ => none
  retLocation? == some (some DataLocation.storage)

def anfHoistFuel : Nat := 100000

mutual

/-- Hoist every nested single-return call out of `e`, returning
    `(counter', preludeStmts, residualExpr)` where `residualExpr` is flat (no
    hoistable call remains nested) and `preludeStmts` are surface `Stmt`s to run,
    in order, before it. -/
def Expr.anfHoist
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name) :
    Nat -> Nat -> Expr -> (Nat × List Stmt × Expr)
  | 0, c, e => (c, [], e)
  | fuel + 1, c, e =>
      let rec1 := Expr.anfHoist functions freeFunctions env externalCallKindEnv
        storageNames fuel
      let recArgs := Args.anfHoist functions freeFunctions env
        externalCallKindEnv storageNames fuel
      let recItems := TupleItems.anfHoist functions freeFunctions env
        externalCallKindEnv storageNames fuel
      let recExprs := Exprs.anfHoist functions freeFunctions env
        externalCallKindEnv storageNames fuel
      match e with
      | Expr.literal _ => (c, [], e)
      | Expr.ident _ => (c, [], e)
      | Expr.typeName _ => (c, [], e)
      | Expr.member base name =>
          let (c1, pre, base') := rec1 c base
          (c1, pre, Expr.member base' name)
      | Expr.index base key =>
          let (c1, p1, base') := rec1 c base
          let (c2, p2, key') := rec1 c1 key
          (c2, p1 ++ p2, Expr.index base' key')
      | Expr.slice base a? b? =>
          let (c1, p1, base') := rec1 c base
          let (c2, p2, a?') :=
            match a? with
            | some a => let (c', p, a') := rec1 c1 a; (c', p, some a')
            | none => (c1, [], none)
          let (c3, p3, b?') :=
            match b? with
            | some b => let (c', p, b') := rec1 c2 b; (c', p, some b')
            | none => (c2, [], none)
          (c3, p1 ++ p2 ++ p3, Expr.slice base' a?' b?')
      | Expr.unary op inner =>
          let (c1, pre, inner') := rec1 c inner
          (c1, pre, Expr.unary op inner')
      | Expr.payableConversion inner =>
          let (c1, pre, inner') := rec1 c inner
          (c1, pre, Expr.payableConversion inner')
      | Expr.enumFromUInt w inner =>
          let (c1, pre, inner') := rec1 c inner
          (c1, pre, Expr.enumFromUInt w inner')
      | Expr.binary op l r =>
          match op with
          | BinaryOp.boolAnd | BinaryOp.boolOr =>
              -- Short-circuit: left unconditional; right operand's effects guarded.
              let (c1, lpre, l') := rec1 c l
              let (c2, rpre, r') := rec1 c1 r
              if rpre.isEmpty then
                (c2, lpre, Expr.binary op l' r')
              else
                let t := anfHoistName c2
                let decl := Stmt.varDecl
                  [{ name := some t, ty := some Ty.bool, location := none }]
                  (some l')
                let cond :=
                  match op with
                  | BinaryOp.boolAnd => Expr.ident t
                  | _ => Expr.unary UnaryOp.logicalNot (Expr.ident t)
                let assign := Stmt.expr
                  (Expr.assign (Expr.ident t) AssignOp.assign r')
                let guard := Stmt.ifElse cond
                  (Stmt.block (rpre ++ [assign])) none
                (c2 + 1, lpre ++ [decl, guard], Expr.ident t)
          | _ =>
              -- Ordinary binary operands: RIGHT then LEFT (solc legacy order).
              let (c1, rpre, r') := rec1 c r
              let (c2, lpre, l') := rec1 c1 l
              if lpre.isEmpty then
                (c2, rpre, Expr.binary op l' r')
              else
                -- The left prelude can mutate state observed by the earlier
                -- evaluated right operand.  Keeping `r'` in the residual
                -- expression would read it only after `lpre` (for example,
                -- `values[wrap(index())] ^ trace`).  Materialize the complete
                -- right value between its own prelude and the left prelude,
                -- preserving Solidity's right-before-left schedule.
                match Expr.abiTyWithInternalFunctionsEnv?
                    functions freeFunctions env r with
                | some rTy =>
                    let t := anfHoistName c2
                    let decl := Stmt.varDecl
                      [{ name := some t, ty := some (Ty.anfTempTy rTy),
                         location := Ty.anfHoistLocation? rTy }]
                      (some r')
                    (c2 + 1, rpre ++ [decl] ++ lpre,
                      Expr.binary op l' (Expr.ident t))
                | none =>
                    -- If the source typer cannot name the right operand, keep
                    -- the conservative prior shape; downstream lowering still
                    -- fails closed rather than inventing a temp type.
                    (c2, rpre ++ lpre, Expr.binary op l' r')
      | Expr.ternary cond a b =>
          let (c1, cpre, cond') := rec1 c cond
          let (c2, apre, a') := rec1 c1 a
          let (c3, bpre, b') := rec1 c2 b
          if apre.isEmpty && bpre.isEmpty then
            (c3, cpre, Expr.ternary cond' a' b')
          else
            match Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env a with
            | some ty =>
                let t := anfHoistName c3
                let decl := Stmt.varDecl
                  [{ name := some t, ty := some (Ty.anfTempTy ty),
                     location := Ty.anfHoistLocation? ty }]
                  none
                let thenB := Stmt.block
                  (apre ++ [Stmt.expr
                    (Expr.assign (Expr.ident t) AssignOp.assign a')])
                let elseB := Stmt.block
                  (bpre ++ [Stmt.expr
                    (Expr.assign (Expr.ident t) AssignOp.assign b')])
                (c3 + 1, cpre ++ [decl, Stmt.ifElse cond' thenB (some elseB)],
                  Expr.ident t)
            | none =>
                -- No resolvable branch type: keep the original (unhoisted)
                -- branches so no hoisted binding is dropped.
                (c1, cpre, Expr.ternary cond' a b)
      | Expr.assign lhs op rhs =>
          -- Assignment RHS effects before LHS-reference effects (solc order).
          let (c1, rpre, rhs') := rec1 c rhs
          let (c2, lpre, lhs') := rec1 c1 lhs
          (c2, rpre ++ lpre, Expr.assign lhs' op rhs')
      | Expr.array elems =>
          let (c1, pre, elems') := recExprs c elems
          (c1, pre, Expr.array elems')
      | Expr.tuple items =>
          let (c1, pre, items') := recItems c items
          (c1, pre, Expr.tuple items')
      | Expr.call callee args =>
          let args := Expr.reorderNamedInternalCallArgs functions freeFunctions
            env callee args
          -- solc's legacy codegen evaluates addmod/mulmod arguments from the
          -- modulus back to the first operand. The generic call schedule is
          -- left-to-right, so hoist side-effecting nested calls in the builtin
          -- order while reconstructing the original positional argument list.
          let (cArgs, apre, args') :=
            match callee, args with
            | Expr.ident name,
                [Arg.positional a, Arg.positional b, Arg.positional m] =>
                if name == "addmod" || name == "mulmod" then
                  let (c1, pm, m') := rec1 c m
                  let (c2, pb, b') := rec1 c1 b
                  let (c3, pa, a') := rec1 c2 a
                  ( c3
                  , pm ++ pb ++ pa
                  , [Arg.positional a', Arg.positional b', Arg.positional m'] )
                else
                  recArgs c args
            | _, _ => recArgs c args
          match Expr.anfHoistableCallTy? functions freeFunctions env
              externalCallKindEnv storageNames (Expr.call callee args) with
          | some retTy =>
              let t := anfHoistName cArgs
              -- R3 (#188): a storage-pointer return hoists to a STORAGE temp.
              let location :=
                if Expr.anfHoistableCallStorageReturn
                    functions freeFunctions env (Expr.call callee args) then
                  some DataLocation.storage
                else
                  Ty.anfHoistLocation? retTy
              let decl := Stmt.varDecl
                [{ name := some t, ty := some (Ty.anfTempTy retTy),
                   location := location }]
                (some (Expr.call callee args'))
              (cArgs + 1, apre ++ [decl], Expr.ident t)
          | none =>
              (cArgs, apre, Expr.call callee args')
      | Expr.callWithOptions callee opts args =>
          match Expr.anfHoistableCallTy? functions freeFunctions env
              externalCallKindEnv storageNames
              (Expr.callWithOptions callee opts args) with
          | some retTy =>
              let (c1, apre, args') := recArgs c args
              let t := anfHoistName c1
              let location :=
                if Expr.anfHoistableCallStorageReturn
                    functions freeFunctions env
                    (Expr.callWithOptions callee opts args) then
                  some DataLocation.storage
                else
                  Ty.anfHoistLocation? retTy
              let decl := Stmt.varDecl
                [{ name := some t, ty := some (Ty.anfTempTy retTy),
                   location := location }]
                (some (Expr.callWithOptions callee opts args'))
              (c1 + 1, apre ++ [decl], Expr.ident t)
          | none =>
              let (c1, apre, args') := recArgs c args
              (c1, apre, Expr.callWithOptions callee opts args')
      | Expr.newExpr ty args =>
          let (c1, apre, args') := recArgs c args
          (c1, apre, Expr.newExpr ty args')
termination_by fuel _ _ => fuel

def Args.anfHoist
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name) :
    Nat -> Nat -> List Arg -> (Nat × List Stmt × List Arg)
  | 0, c, args => (c, [], args)
  | _, c, [] => (c, [], [])
  | fuel + 1, c, arg :: rest =>
      let (c1, p1, arg') :=
        match arg with
        | Arg.positional e =>
            let (c', p, e') := Expr.anfHoist functions freeFunctions env
              externalCallKindEnv storageNames fuel c e
            (c', p, Arg.positional e')
        | Arg.named n e =>
            let (c', p, e') := Expr.anfHoist functions freeFunctions env
              externalCallKindEnv storageNames fuel c e
            (c', p, Arg.named n e')
      let (c2, p2, rest') := Args.anfHoist functions freeFunctions env
        externalCallKindEnv storageNames fuel c1 rest
      if p2.isEmpty then
        (c2, p1, arg' :: rest')
      else
        -- A later argument's hoisted call can mutate state observed by this
        -- earlier argument.  Evaluating only `p1` now and leaving `arg'` in the
        -- residual call would therefore reorder `combine(trace, mutate())` to
        -- run `mutate()` before reading `trace`.  Materialize the complete
        -- earlier argument between its own prelude and the later argument's
        -- prelude, matching Solidity's left-to-right call-argument evaluation.
        let argExpr :=
          match arg' with
          | Arg.positional e => e
          | Arg.named _ e => e
        match Expr.abiTyWithInternalFunctionsEnv?
            functions freeFunctions env argExpr with
        | some argTy =>
            let t := anfHoistName c2
            let decl := Stmt.varDecl
              [{ name := some t, ty := some (Ty.anfTempTy argTy),
                 location := Ty.anfHoistLocation? argTy }]
              (some argExpr)
            (c2 + 1, p1 ++ [decl] ++ p2,
              Arg.withExpr (Expr.ident t) arg' :: rest')
        | none =>
            -- Keep the prior conservative result when the surface typer cannot
            -- name a temp type; the downstream lowering will still fail closed
            -- rather than inventing an ill-typed binding.
            (c2, p1 ++ p2, arg' :: rest')
termination_by fuel _ _ => fuel

def Exprs.anfHoist
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name) :
    Nat -> Nat -> List Expr -> (Nat × List Stmt × List Expr)
  | 0, c, es => (c, [], es)
  | _, c, [] => (c, [], [])
  | fuel + 1, c, e :: rest =>
      let (c1, p1, e') := Expr.anfHoist functions freeFunctions env
        externalCallKindEnv storageNames fuel c e
      let (c2, p2, rest') := Exprs.anfHoist functions freeFunctions env
        externalCallKindEnv storageNames fuel c1 rest
      (c2, p1 ++ p2, e' :: rest')
termination_by fuel _ _ => fuel

def TupleItems.anfHoist
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name) :
    Nat -> Nat -> List TupleItem -> (Nat × List Stmt × List TupleItem)
  | 0, c, items => (c, [], items)
  | _, c, [] => (c, [], [])
  | fuel + 1, c, item :: rest =>
      let (c1, p1, item') :=
        match item with
        | TupleItem.hole => (c, [], TupleItem.hole)
        | TupleItem.value e =>
            let (c', p, e') := Expr.anfHoist functions freeFunctions env
              externalCallKindEnv storageNames fuel c e
            (c', p, TupleItem.value e')
      let (c2, p2, rest') := TupleItems.anfHoist functions freeFunctions env
        externalCallKindEnv storageNames fuel c1 rest
      (c2, p1 ++ p2, item' :: rest')
termination_by fuel _ _ => fuel

end

/-- STAGE-D #195: hoist an `emit E(args…)` statement's arguments into temps bound
    in solc's TWO-PHASE order — indexed/topic positions in REVERSE source order
    first, then non-indexed/data positions in FORWARD source order
    (`ExpressionCompiler.cpp` `Kind::Event`). The interpreter already implements
    this schedule (R1), but the statement-level call hoister flattens the
    call-args into temps in plain source L2R order, so the schedule only ever
    sees temp READS and the two-phase order is lost. Here each argument is hoisted
    in SCHEDULE order (so the temp-binding side effects run two-phase), while the
    rebuilt `emit` reads the temps POSITIONALLY (the interpreter encodes
    positionally). An event whose indexed positions are a source-order prefix
    (all-data, or indexed-at-front) yields the identity schedule, so its hoist is
    byte-identical to the generic L2R one. Returns `none` (caller falls back to
    the generic hoister) for a non-`emit(ident …)` shape, an unknown event, an
    arity/flag mismatch, or any named argument. -/
def emitTwoPhaseHoist?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (eventIndexedEnv : EventIndexedEnv) :
    Expr -> Option (List Stmt × Expr)
  | Expr.call (Expr.ident evName) args =>
      match List.lookup evName eventIndexedEnv with
      | some flags =>
          let allPositional :=
            args.all (fun a => match a with
              | Arg.positional _ => true
              | Arg.named _ _ => false)
          if flags.length == args.length && allPositional then
            let n := args.length
            let positions := List.range n
            let indexedPositions :=
              (positions.filter (fun i => flags.getD i false)).reverse
            let dataPositions := positions.filter (fun i => !(flags.getD i false))
            let schedule := indexedPositions ++ dataPositions
            -- Identity schedule (all-data, or indexed args forming a reversed
            -- prefix) ⇒ the two-phase order IS source L2R; decline so the
            -- caller keeps the generic hoister (and, in `Stmt.anfPreprocess`,
            -- the green direct-lowering path stays byte-identical).
            if schedule == positions then none else
            let step := fun (acc : Nat × List Stmt × List (Nat × Expr)) (pos : Nat) =>
              let (c, pre, residuals) := acc
              match args[pos]? with
              | some (Arg.positional e) =>
                  let (c', p, e') :=
                    Expr.anfHoist functions freeFunctions env externalCallKindEnv
                      storageNames anfHoistFuel c e
                  (c', pre ++ p, residuals ++ [(pos, e')])
              | _ => acc
            let (_, prelude, residuals) := schedule.foldl step (0, [], [])
            let newArgs := positions.map (fun pos =>
              match List.lookup pos residuals with
              | some e => Arg.positional e
              | none =>
                  match args[pos]? with
                  | some a => a
                  | none => Arg.positional (Expr.ident "_"))
            if prelude.isEmpty then none
            else some (prelude, Expr.call (Expr.ident evName) newArgs)
          else none
      | none => none
  | _ => none

/-- Hoist a statement's OWN top-level expression positions (return value,
    expr-statement target, var-decl initializer, if/emit/revert operands) into a
    prelude, returning a `block` when any hoisting happened, else `none`. Child
    statements are handled separately by `Stmt.anfPreprocess`. -/
def Stmt.anfNormalizeSelf?
    (structEnv : StructEnv)
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (eventIndexedEnv : EventIndexedEnv) :
    Stmt -> Option Stmt :=
  let hoist := fun (e : Expr) =>
    Expr.anfHoist functions freeFunctions env externalCallKindEnv storageNames
      anfHoistFuel 0 e
  -- Re-run the struct-resolution and abi-annotation passes on the produced
  -- block: both ran on the function body BEFORE this hoisting, so any residual
  -- that reads a fresh hoist temp (`abi.encode(_sol_hoist_n)`, a struct member
  -- `_sol_hoist_n.field`, or a `T storage`/`Ty.user` temp type) is otherwise
  -- UNRESOLVED and fails to lower. `resolveStructs` threads a type env through
  -- the block's varDecls so a struct-typed hoist temp resolves its member
  -- accesses to ordinal indices; `annotateAbi` likewise annotates a hoisted abi
  -- argument's element type. Both fire only when the enumerated dispatcher
  -- already declined `stmt` (never a green statement), so green cases are
  -- untouched.
  let done := fun (pre : List Stmt) (tail : Stmt) =>
    some (Stmt.annotateAbi env
      (Stmt.resolveStructs structEnv env (Stmt.block (pre ++ [tail]))))
  fun stmt =>
  match stmt with
  | Stmt.returnValues (some e) =>
      let (_, pre, e') := hoist e
      if pre.isEmpty then none else done pre (Stmt.returnValues (some e'))
  | Stmt.expr e =>
      let (_, pre, e') := hoist e
      if pre.isEmpty then none else done pre (Stmt.expr e')
  | Stmt.varDecl bindings (some e) =>
      let (_, pre, e') := hoist e
      if pre.isEmpty then none else done pre (Stmt.varDecl bindings (some e'))
  | Stmt.ifElse c t e =>
      let (_, pre, c') := hoist c
      if pre.isEmpty then none else done pre (Stmt.ifElse c' t e)
  | Stmt.emitEvent e =>
      -- STAGE-D #195: two-phase emit-arg schedule (indexed reverse, then data
      -- forward). Falls back to the generic L2R hoist when the event is unknown
      -- or the shape is unsupported; the identity schedule reproduces it exactly.
      match emitTwoPhaseHoist? functions freeFunctions env externalCallKindEnv
          storageNames eventIndexedEnv e with
      | some (pre, e') =>
          if pre.isEmpty then none else done pre (Stmt.emitEvent e')
      | none =>
          let (_, pre, e') := hoist e
          if pre.isEmpty then none else done pre (Stmt.emitEvent e')
  | Stmt.revertCall e =>
      let (_, pre, e') := hoist e
      if pre.isEmpty then none else done pre (Stmt.revertCall e')
  | _ => none

end SolidCore.Solidity.Executable
