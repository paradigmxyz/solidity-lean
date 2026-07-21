// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract FnValueShadowingHarnessTarget {
    function x() internal pure returns (uint256) {
        return 42;
    }

    // Param shadows the function name: `x` in value position is the PARAM.
    function go(uint256 x) external pure returns (uint256) {
        return x + 1;
    }

    // Local declaration shadows the function name.
    function localShadow() external pure returns (uint256) {
        uint256 x = 7;
        return x * 2;
    }

    // For-loop binding shadows the function name.
    function loopShadow(uint256 a) external pure returns (uint256) {
        uint256 r = 0;
        for (uint256 x = 0; x < a; x++) {
            r += x;
        }
        return r;
    }

    // Nested scopes: the inner-block local shadows only inside its block; the
    // call after the block resolves to the FUNCTION x again.
    function nestedScopes() external pure returns (uint256) {
        uint256 acc = 0;
        {
            uint256 x = 5;
            acc = x;
        }
        acc += x();
        return acc;
    }

    // Control: NON-shadowing function-value references must keep lowering to
    // their dispatch IDs (data-dependent function-pointer select).
    function a1() internal pure returns (uint256) {
        return 11;
    }

    function a2() internal pure returns (uint256) {
        return 22;
    }

    function select(bool c) external pure returns (uint256) {
        function() internal pure returns (uint256) p = c ? a1 : a2;
        return p();
    }
}
