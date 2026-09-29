// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

contract UninitializedFnPtrComparisonTarget {
    function internal1() internal pure returns (bool) {}

    function equal()
        external
        pure
        returns (bool same, bool diff, bool inv)
    {
        function() internal pure returns (bool) invalid;
        inv = internal1 == invalid;
    }

    function callInvalid() external pure returns (bool) {
        function() internal pure returns (bool) invalid;
        return invalid();
    }
}
