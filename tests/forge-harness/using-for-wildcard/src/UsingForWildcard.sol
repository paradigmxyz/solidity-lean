// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// G20 pin (docs/solidity-lean-solc-deep-comparison.md): `using Lib for *` WILDCARD
// binding attaches the library's functions to ALL types by their first
// parameter. A member call through the wildcard binding dispatches to the
// library function for whatever receiver type matches. Pin correct dispatch
// across several receiver types.
library WildcardLib {
    function double(uint256 x) internal pure returns (uint256) {
        return 2 * x;
    }

    function tripleI(int256 x) internal pure returns (int256) {
        return 3 * x;
    }

    function lenPlus(bytes memory b, uint256 y) internal pure returns (uint256) {
        return b.length + y;
    }

    function flip(bool b) internal pure returns (bool) {
        return !b;
    }
}

contract UsingForWildcardHarnessTarget {
    using WildcardLib for *;

    // uint256 receiver -> WildcardLib.double
    function viaUint(uint256 x) public pure returns (uint256) {
        return x.double();
    }

    // int256 receiver -> WildcardLib.tripleI
    function viaInt(int256 x) public pure returns (int256) {
        return x.tripleI();
    }

    // bytes memory receiver (with extra arg) -> WildcardLib.lenPlus
    function viaBytes(bytes memory b, uint256 y) public pure returns (uint256) {
        return b.lenPlus(y);
    }

    // bool receiver -> WildcardLib.flip
    function viaBool(bool b) public pure returns (bool) {
        return b.flip();
    }
}
