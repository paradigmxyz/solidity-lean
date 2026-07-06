// SPDX-License-Identifier: BSD-3-Clause
pragma solidity ^0.8.20;

// Import-free, assembly-free Compound Protocol ExponentialNoError slice.
// The core contract is adapted from Compound's ExponentialNoError module; the
// harness below exposes selected internal helpers for paired Forge/Lean checks.
contract CompoundExponentialNoError {
    uint256 constant expScale = 1e18;
    uint256 constant doubleScale = 1e36;
    uint256 constant halfExpScale = expScale / 2;
    uint256 constant mantissaOne = expScale;

    struct Exp {
        uint256 mantissa;
    }

    struct Double {
        uint256 mantissa;
    }

    function truncate(Exp memory exp) internal pure returns (uint256) {
        return exp.mantissa / expScale;
    }

    function mul_ScalarTruncate(Exp memory a, uint256 scalar)
        internal
        pure
        returns (uint256)
    {
        Exp memory product = mul_(a, scalar);
        return truncate(product);
    }

    function mul_ScalarTruncateAddUInt(
        Exp memory a,
        uint256 scalar,
        uint256 addend
    ) internal pure returns (uint256) {
        Exp memory product = mul_(a, scalar);
        return add_(truncate(product), addend);
    }

    function lessThanExp(Exp memory left, Exp memory right)
        internal
        pure
        returns (bool)
    {
        return left.mantissa < right.mantissa;
    }

    function lessThanOrEqualExp(Exp memory left, Exp memory right)
        internal
        pure
        returns (bool)
    {
        return left.mantissa <= right.mantissa;
    }

    function greaterThanExp(Exp memory left, Exp memory right)
        internal
        pure
        returns (bool)
    {
        return left.mantissa > right.mantissa;
    }

    function isZeroExp(Exp memory value) internal pure returns (bool) {
        return value.mantissa == 0;
    }

    function safe224(uint256 n, string memory errorMessage)
        internal
        pure
        returns (uint224)
    {
        require(n < 2 ** 224, errorMessage);
        return uint224(n);
    }

    function safe32(uint256 n, string memory errorMessage)
        internal
        pure
        returns (uint32)
    {
        require(n < 2 ** 32, errorMessage);
        return uint32(n);
    }

    function add_(Exp memory a, Exp memory b)
        internal
        pure
        returns (Exp memory)
    {
        return Exp({mantissa: add_(a.mantissa, b.mantissa)});
    }

    function add_(Double memory a, Double memory b)
        internal
        pure
        returns (Double memory)
    {
        return Double({mantissa: add_(a.mantissa, b.mantissa)});
    }

    function add_(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    function sub_(Exp memory a, Exp memory b)
        internal
        pure
        returns (Exp memory)
    {
        return Exp({mantissa: sub_(a.mantissa, b.mantissa)});
    }

    function sub_(Double memory a, Double memory b)
        internal
        pure
        returns (Double memory)
    {
        return Double({mantissa: sub_(a.mantissa, b.mantissa)});
    }

    function sub_(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    function mul_(Exp memory a, Exp memory b)
        internal
        pure
        returns (Exp memory)
    {
        return Exp({mantissa: mul_(a.mantissa, b.mantissa) / expScale});
    }

    function mul_(Exp memory a, uint256 b)
        internal
        pure
        returns (Exp memory)
    {
        return Exp({mantissa: mul_(a.mantissa, b)});
    }

    function mul_(uint256 a, Exp memory b)
        internal
        pure
        returns (uint256)
    {
        return mul_(a, b.mantissa) / expScale;
    }

    function mul_(Double memory a, Double memory b)
        internal
        pure
        returns (Double memory)
    {
        return Double({mantissa: mul_(a.mantissa, b.mantissa) / doubleScale});
    }

    function mul_(Double memory a, uint256 b)
        internal
        pure
        returns (Double memory)
    {
        return Double({mantissa: mul_(a.mantissa, b)});
    }

    function mul_(uint256 a, Double memory b)
        internal
        pure
        returns (uint256)
    {
        return mul_(a, b.mantissa) / doubleScale;
    }

    function mul_(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    function div_(Exp memory a, Exp memory b)
        internal
        pure
        returns (Exp memory)
    {
        return Exp({mantissa: div_(mul_(a.mantissa, expScale), b.mantissa)});
    }

    function div_(Exp memory a, uint256 b)
        internal
        pure
        returns (Exp memory)
    {
        return Exp({mantissa: div_(a.mantissa, b)});
    }

    function div_(uint256 a, Exp memory b)
        internal
        pure
        returns (uint256)
    {
        return div_(mul_(a, expScale), b.mantissa);
    }

    function div_(Double memory a, Double memory b)
        internal
        pure
        returns (Double memory)
    {
        return Double({mantissa: div_(mul_(a.mantissa, doubleScale), b.mantissa)});
    }

    function div_(Double memory a, uint256 b)
        internal
        pure
        returns (Double memory)
    {
        return Double({mantissa: div_(a.mantissa, b)});
    }

    function div_(uint256 a, Double memory b)
        internal
        pure
        returns (uint256)
    {
        return div_(mul_(a, doubleScale), b.mantissa);
    }

    function div_(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    function fraction(uint256 a, uint256 b)
        internal
        pure
        returns (Double memory)
    {
        return Double({mantissa: div_(mul_(a, doubleScale), b)});
    }
}

contract CompoundExponentialNoErrorHarness is CompoundExponentialNoError {
    function scalarSummary(uint256 mantissa, uint256 scalar, uint256 addend)
        external
        pure
        returns (
            uint256 truncated,
            uint256 scaled,
            uint256 scaledPlus
        )
    {
        Exp memory value = Exp({mantissa: mantissa});
        return (
            truncate(value),
            mul_ScalarTruncate(value, scalar),
            mul_ScalarTruncateAddUInt(value, scalar, addend)
        );
    }

    function compareSummary(uint256 leftMantissa, uint256 rightMantissa)
        external
        pure
        returns (
            bool less,
            bool lessOrEqual,
            bool greater,
            bool zeroValue
        )
    {
        Exp memory left = Exp({mantissa: leftMantissa});
        Exp memory right = Exp({mantissa: rightMantissa});
        return (
            lessThanExp(left, right),
            lessThanOrEqualExp(left, right),
            greaterThanExp(right, left),
            isZeroExp(Exp({mantissa: 0}))
        );
    }

    function expArithmetic(
        uint256 leftMantissa,
        uint256 rightMantissa
    )
        external
        pure
        returns (
            uint256 added,
            uint256 subtracted,
            uint256 multiplied,
            uint256 divided
        )
    {
        Exp memory left = Exp({mantissa: leftMantissa});
        Exp memory right = Exp({mantissa: rightMantissa});
        Exp memory sum = add_(left, right);
        Exp memory difference = sub_(right, left);
        Exp memory product = mul_(left, right);
        Exp memory quotient = div_(right, left);
        return (
            sum.mantissa,
            difference.mantissa,
            product.mantissa,
            quotient.mantissa
        );
    }

    function expScalarProducts(
        uint256 mantissa,
        uint256 scalar
    ) external pure returns (uint256 scalarProduct, uint256 uintTimesExp) {
        Exp memory value = Exp({mantissa: mantissa});
        Exp memory scaled = mul_(value, scalar);
        return (
            scaled.mantissa,
            mul_(scalar, value)
        );
    }

    function doubleArithmetic(
        uint256 leftMantissa,
        uint256 rightMantissa
    )
        external
        pure
        returns (
            uint256 added,
            uint256 subtracted,
            uint256 multiplied,
            uint256 divided
        )
    {
        Double memory left = Double({mantissa: leftMantissa});
        Double memory right = Double({mantissa: rightMantissa});
        Double memory sum = add_(left, right);
        Double memory difference = sub_(right, left);
        Double memory product = mul_(left, right);
        Double memory quotient = div_(right, left);
        return (
            sum.mantissa,
            difference.mantissa,
            product.mantissa,
            quotient.mantissa
        );
    }

    function doubleScalarProducts(
        uint256 mantissa,
        uint256 scalar
    ) external pure returns (uint256 scalarProduct, uint256 uintTimesDouble) {
        Double memory value = Double({mantissa: mantissa});
        Double memory scaled = mul_(value, scalar);
        return (
            scaled.mantissa,
            mul_(scalar, value)
        );
    }

    function fractionMantissa(uint256 numerator, uint256 denominator)
        external
        pure
        returns (uint256)
    {
        Double memory value = fraction(numerator, denominator);
        return value.mantissa;
    }

    function safeDowncastSummary(uint256 n)
        external
        pure
        returns (uint224 as224, uint32 as32)
    {
        return (safe224(n, "safe224 overflow"), safe32(n, "safe32 overflow"));
    }

    function safe224Public(uint256 n) external pure returns (uint224) {
        return safe224(n, "safe224 overflow");
    }

    function safe32Public(uint256 n) external pure returns (uint32) {
        return safe32(n, "safe32 overflow");
    }
}
