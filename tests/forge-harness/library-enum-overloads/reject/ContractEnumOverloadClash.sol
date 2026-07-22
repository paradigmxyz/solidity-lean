// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CONTRACT-level control: the same enum-distinct overload pair collides in
// the external ABI (both params erase to `uint8`) — solc REJECTS it with
// "Function overload clash during conversion to external types for
// arguments." The library twin in ../src is ACCEPTED.

contract ContractEnumOverloadClash {
    enum EnumA { A0, A1 }
    enum EnumB { B0, B1, B2 }

    function f(EnumA a) public pure returns (uint256) {
        return 100 + uint256(uint8(a));
    }

    function f(EnumB b) public pure returns (uint256) {
        return 200 + uint256(uint8(b));
    }
}
