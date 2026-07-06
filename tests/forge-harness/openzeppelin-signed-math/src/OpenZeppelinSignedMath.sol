// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-free adaptation of OpenZeppelin Contracts v5.6.1
// `utils/math/SignedMath.sol`, with the one needed SafeCast bool helper
// inlined to keep import resolution out of scope.
library OpenZeppelinSignedMathSafeCast {
    function toUint(bool value) internal pure returns (uint256) {
        return value ? 1 : 0;
    }
}

library OpenZeppelinSignedMath {
    function ternary(bool condition, int256 a, int256 b)
        internal
        pure
        returns (int256)
    {
        unchecked {
            return b ^
                (
                    (a ^ b) *
                        int256(OpenZeppelinSignedMathSafeCast.toUint(condition))
                );
        }
    }

    function max(int256 a, int256 b) internal pure returns (int256) {
        return ternary(a > b, a, b);
    }

    function min(int256 a, int256 b) internal pure returns (int256) {
        return ternary(a < b, a, b);
    }

    function average(int256 a, int256 b) internal pure returns (int256) {
        int256 x = (a & b) + ((a ^ b) >> 1);
        return x + (int256(uint256(x) >> 255) & (a ^ b));
    }

    function abs(int256 n) internal pure returns (uint256) {
        unchecked {
            int256 mask = n >> 255;
            return uint256((n + mask) ^ mask);
        }
    }
}

contract OpenZeppelinSignedMathHarness {
    function ternary(bool condition, int256 a, int256 b)
        external
        pure
        returns (int256)
    {
        return OpenZeppelinSignedMath.ternary(condition, a, b);
    }

    function max(int256 a, int256 b) external pure returns (int256) {
        return OpenZeppelinSignedMath.max(a, b);
    }

    function min(int256 a, int256 b) external pure returns (int256) {
        return OpenZeppelinSignedMath.min(a, b);
    }

    function average(int256 a, int256 b) external pure returns (int256) {
        return OpenZeppelinSignedMath.average(a, b);
    }

    function abs(int256 value) external pure returns (uint256) {
        return OpenZeppelinSignedMath.abs(value);
    }

    function summary(int256 a, int256 b)
        external
        pure
        returns (
            int256 high,
            int256 low,
            int256 mean,
            uint256 absA,
            uint256 absB
        )
    {
        high = OpenZeppelinSignedMath.max(a, b);
        low = OpenZeppelinSignedMath.min(a, b);
        mean = OpenZeppelinSignedMath.average(a, b);
        absA = OpenZeppelinSignedMath.abs(a);
        absB = OpenZeppelinSignedMath.abs(b);
    }
}
