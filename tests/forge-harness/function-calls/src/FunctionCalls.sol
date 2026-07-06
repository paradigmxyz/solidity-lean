// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract FunctionCallHarnessTarget {
    function namedFallthrough(uint256 x)
        external
        pure
        returns (uint256 out)
    {
        out = double(x);
    }

    function defaultNamedReturn()
        external
        pure
        returns (uint256 out)
    {
    }

    function namedArgumentOrder(uint256 x)
        external
        pure
        returns (uint256)
    {
        return mix({right: x, left: 4});
    }

    function double(uint256 x) internal pure returns (uint256) {
        return x * 2;
    }

    function mix(uint256 left, uint256 right)
        internal
        pure
        returns (uint256 out)
    {
        out = left * 100 + right;
    }
}
