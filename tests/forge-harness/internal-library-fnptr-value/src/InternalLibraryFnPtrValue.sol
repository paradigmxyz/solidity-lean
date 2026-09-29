// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

library L {
    function f() internal returns (uint256) {}
}

contract InternalLibraryFnPtrValueTarget {
    function assignOnly() external returns (uint256) {
        function() internal returns (uint256) ptr;
        ptr = L.f;
    }

    function assignAndCall() external returns (uint256) {
        function() internal returns (uint256) ptr;
        ptr = L.f;
        return ptr();
    }
}
