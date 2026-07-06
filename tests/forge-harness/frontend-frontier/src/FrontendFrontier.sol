// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

/// User-defined value type metadata.
type FrontendFrontierId is uint256;

uint256 constant FRONTEND_FRONTIER_DOC_CONSTANT = 1;

/// Enum metadata.
enum FrontendFrontierMode {
    Off,
    On
}

/// Struct metadata.
struct FrontendFrontierBox {
    uint256 value;
}

/// Event metadata.
event FrontendFrontierEvent(uint256 indexed value);

event FrontendFrontierAnonymous(uint256 indexed value) anonymous;

/// Error metadata.
error FrontendFrontierError(uint256 value);

function frontendFrontierPlusOne(uint256 value) pure returns (uint256) {
    return value + 1;
}

function frontendFrontierIdAdd(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(
        FrontendFrontierId.unwrap(lhs) + FrontendFrontierId.unwrap(rhs)
    );
}

function frontendFrontierIdSub(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(
        FrontendFrontierId.unwrap(lhs) - FrontendFrontierId.unwrap(rhs)
    );
}

function frontendFrontierIdMul(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(
        FrontendFrontierId.unwrap(lhs) * FrontendFrontierId.unwrap(rhs)
    );
}

function frontendFrontierIdDiv(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(
        FrontendFrontierId.unwrap(lhs) / FrontendFrontierId.unwrap(rhs)
    );
}

function frontendFrontierIdMod(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(
        FrontendFrontierId.unwrap(lhs) % FrontendFrontierId.unwrap(rhs)
    );
}

function frontendFrontierIdAnd(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(
        FrontendFrontierId.unwrap(lhs) & FrontendFrontierId.unwrap(rhs)
    );
}

function frontendFrontierIdOr(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(
        FrontendFrontierId.unwrap(lhs) | FrontendFrontierId.unwrap(rhs)
    );
}

function frontendFrontierIdXor(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(
        FrontendFrontierId.unwrap(lhs) ^ FrontendFrontierId.unwrap(rhs)
    );
}

function frontendFrontierIdEq(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (bool) {
    return FrontendFrontierId.unwrap(lhs) == FrontendFrontierId.unwrap(rhs);
}

function frontendFrontierIdNe(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (bool) {
    return FrontendFrontierId.unwrap(lhs) != FrontendFrontierId.unwrap(rhs);
}

function frontendFrontierIdLt(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (bool) {
    return FrontendFrontierId.unwrap(lhs) < FrontendFrontierId.unwrap(rhs);
}

function frontendFrontierIdGt(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (bool) {
    return FrontendFrontierId.unwrap(lhs) > FrontendFrontierId.unwrap(rhs);
}

function frontendFrontierIdLe(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (bool) {
    return FrontendFrontierId.unwrap(lhs) <= FrontendFrontierId.unwrap(rhs);
}

function frontendFrontierIdGe(
    FrontendFrontierId lhs,
    FrontendFrontierId rhs
) pure returns (bool) {
    return FrontendFrontierId.unwrap(lhs) >= FrontendFrontierId.unwrap(rhs);
}

function frontendFrontierIdNeg(
    FrontendFrontierId value
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(100 - FrontendFrontierId.unwrap(value));
}

function frontendFrontierIdBitNot(
    FrontendFrontierId value
) pure returns (FrontendFrontierId) {
    return FrontendFrontierId.wrap(255 ^ FrontendFrontierId.unwrap(value));
}

using {frontendFrontierPlusOne} for uint256;
using {
    frontendFrontierIdAdd as +,
    frontendFrontierIdSub as -,
    frontendFrontierIdMul as *,
    frontendFrontierIdDiv as /,
    frontendFrontierIdMod as %,
    frontendFrontierIdAnd as &,
    frontendFrontierIdOr as |,
    frontendFrontierIdXor as ^,
    frontendFrontierIdEq as ==,
    frontendFrontierIdNe as !=,
    frontendFrontierIdLt as <,
    frontendFrontierIdGt as >,
    frontendFrontierIdLe as <=,
    frontendFrontierIdGe as >=,
    frontendFrontierIdNeg as -,
    frontendFrontierIdBitNot as ~
} for FrontendFrontierId global;

/// Parser metadata that should not affect the abstract source semantics.
abstract contract FrontendFrontierBase {
    /// Public variable override target.
    function value() external view virtual returns (uint256);

    /// Ordinary function override target.
    function compute(uint256 x) public view virtual returns (uint256);
}

abstract contract FrontendFrontierLeftBase {
    function pick() public pure virtual returns (uint256) {
        return 1;
    }
}

abstract contract FrontendFrontierRightBase {
    function pick() public pure virtual returns (uint256) {
        return 2;
    }
}

contract FrontendFrontierImpl is FrontendFrontierBase {
    uint256 constant SIZE = 3;
    /// State variable metadata.
    uint256 public override value;
    uint256[SIZE] public values;

    constructor(uint256 seed) {
        value = seed;
        values[0] = 1;
        values[1] = 2;
        values[2] = 3;
    }

    function compute(uint256 x) public view override returns (uint256) {
        return x + value + 1 minutes / 60 seconds;
    }

    function sumValues() external view returns (uint256) {
        return values[0] + values[1] + values[2];
    }
}

contract FrontendFrontierOverrideDiamond is
    FrontendFrontierLeftBase,
    FrontendFrontierRightBase
{
    function pick()
        public
        pure
        override(FrontendFrontierLeftBase, FrontendFrontierRightBase)
        returns (uint256)
    {
        return 9;
    }
}

contract FrontendFrontierModifierBase {
    /// Modifier metadata.
    modifier gate() virtual {
        _;
    }
}

contract FrontendFrontierModifierOverride is FrontendFrontierModifierBase {
    modifier gate() override {
        _;
    }

    function gated() external gate returns (uint256) {
        return 11;
    }
}

interface FrontendFrontierInterface {
    function ifaceValue() external view returns (uint256);
}

contract FrontendFrontierInterfaceImpl is FrontendFrontierInterface {
    function privateDouble(uint256 value) private pure returns (uint256) {
        return value * 2;
    }

    function ifaceValue() external view override returns (uint256) {
        return privateDouble(39);
    }
}

contract FrontendFrontierUsingFunctionList {
    function run(uint256 value) external pure returns (uint256) {
        return value.frontendFrontierPlusOne();
    }
}

contract FrontendFrontierGlobalUsing {
    function run(uint256 lhs, uint256 rhs) external pure returns (uint256) {
        FrontendFrontierId left = FrontendFrontierId.wrap(lhs);
        FrontendFrontierId right = FrontendFrontierId.wrap(rhs);
        return FrontendFrontierId.unwrap(left + right);
    }

    function operatorSweep() external pure returns (uint256) {
        FrontendFrontierId left = FrontendFrontierId.wrap(42);
        FrontendFrontierId right = FrontendFrontierId.wrap(10);
        uint256 total = FrontendFrontierId.unwrap(left + right)
            + FrontendFrontierId.unwrap(left - right)
            + FrontendFrontierId.unwrap(left * right)
            + FrontendFrontierId.unwrap(left / right)
            + FrontendFrontierId.unwrap(left % right)
            + FrontendFrontierId.unwrap(left & right)
            + FrontendFrontierId.unwrap(left | right)
            + FrontendFrontierId.unwrap(left ^ right)
            + FrontendFrontierId.unwrap(-right)
            + FrontendFrontierId.unwrap(~right);
        if (left == left) total += 1;
        if (left != right) total += 2;
        if (right < left) total += 4;
        if (left > right) total += 8;
        if (right <= left) total += 16;
        if (left >= right) total += 32;
        return total;
    }
}

contract FrontendFrontierScalarOps {
    function operatorFrontier() external pure returns (uint256) {
        uint256 x = 17;
        x -= 2;
        x *= 4;
        x /= 3;
        x %= 7;
        x &= 5;
        x |= 8;
        x ^= 3;
        x <<= 2;
        x >>= 1;

        uint256 y = 2 ** 5;
        uint256 z = (uint256(7) - 3)
            + (uint256(10) % 6)
            + (uint256(1) << 3)
            + (uint256(16) >> 2)
            + (uint256(5) & 3)
            + (uint256(4) | 1)
            + (uint256(6) ^ 3);
        bool ok = (x != y) && (x <= 30) && (x >= 30);
        if (!ok) {
            return 0;
        }
        return x + y + z;
    }

    function unitFrontier() external pure returns (uint256) {
        return 1 wei
            + 2 gwei / 1 gwei
            + 3 ether / 1 ether
            + 4 hours / 1 hours
            + 5 days / 1 days
            + 6 weeks / 1 weeks;
    }
}

contract FrontendFrontierScalarValues {
    uint256 public immutable immutableValue;
    uint256 transient transientValue;
    uint256[] internal stored;

    constructor(uint256 seed) {
        immutableValue = seed;
        stored.push(seed);
    }

    function storageRef() external returns (uint256) {
        uint256[] storage ref = stored;
        ref[0] += 1;
        return ref[0];
    }

    function transientRoundTrip(uint256 value) external returns (uint256) {
        transientValue = value;
        return transientValue;
    }

    function transientWrite(uint256 value) external {
        transientValue = value;
    }

    function transientRead() external view returns (uint256) {
        return transientValue;
    }
}

contract FrontendFrontierConstructorUsing {
    uint256 public result;

    constructor(uint256 seed) {
        FrontendFrontierId left = FrontendFrontierId.wrap(seed);
        FrontendFrontierId right = FrontendFrontierId.wrap(2);
        result = FrontendFrontierId.unwrap(left + right)
            + seed.frontendFrontierPlusOne();
    }
}

contract FrontendFrontierFunctionTypeVariants {
    function internalPureTarget(uint256 value)
        internal
        pure
        returns (uint256)
    {
        return value + 1;
    }

    function acceptInternalPure(
        function(uint256) internal pure returns (uint256) fn,
        uint256 value
    ) internal pure returns (uint256) {
        return fn(value);
    }

    function internalPureRun(uint256 value) external pure returns (uint256) {
        return acceptInternalPure(internalPureTarget, value);
    }

    function acceptExternalNonpayable(
        function(uint256) external returns (uint256) fn
    ) external pure returns (bool) {
        return true;
    }

    function acceptExternalPayable(
        function(uint256) external payable returns (uint256) fn
    ) external pure returns (bool) {
        return true;
    }
}

contract FrontendFrontierFunctionTypes {
    function callGetter(function() external view returns (uint256) getter)
        external
        view
        returns (uint256)
    {
        return getter();
    }

    function same(
        function() external view returns (uint256) lhs,
        function() external view returns (uint256) rhs
    ) external pure returns (bool) {
        return lhs == rhs;
    }

    function literalFrontier()
        external
        pure
        returns (bytes memory, string memory, uint256)
    {
        return (hex"1234", unicode"hi", 2 minutes);
    }
}
