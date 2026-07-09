// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: reading a storage array past its length must revert with
// Panic(0x32) (array out-of-bounds). Non-arithmetic panic path (bounds check),
// distinct from overflow(0x11)/div-zero(0x12). Also exercises a constructor-
// populated dynamic storage array + a view read. A code mismatch or a
// wrong/empty revert here would be a fake wrong-revert gap.
contract Indexer {
    uint256[] private arr;

    constructor() {
        arr.push(10);
        arr.push(20);
    }

    function f(uint256 i) external view returns (uint256) {
        return arr[i];
    }
}
