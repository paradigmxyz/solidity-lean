// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// BUG#6 acceptance side: two public LIBRARY overloads whose params differ only
// by enum TYPE are solc-ACCEPTED — their library-qualified signatures
// (`f(OvLib.EnumA)` / `f(OvLib.EnumB)`) are distinct even though both erase to
// `f(uint8)` in the external ABI. The same pair at CONTRACT level is
// solc-REJECTED ("Function overload clash during conversion to external
// types") — see this lane's `reject/` control.

library OvLib {
    enum EnumA { A0, A1 }
    enum EnumB { B0, B1, B2 }

    function f(EnumA a) public pure returns (uint256) {
        return 100 + uint256(uint8(a));
    }

    function f(EnumB b) public pure returns (uint256) {
        return 200 + uint256(uint8(b));
    }
}

contract LibraryEnumOverloadsHarnessTarget {
    function callA(uint8 a) external pure returns (uint256) {
        return OvLib.f(OvLib.EnumA(a));
    }

    function callB(uint8 b) external pure returns (uint256) {
        return OvLib.f(OvLib.EnumB(b));
    }
}
