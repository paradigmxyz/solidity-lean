// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// AGG1: a `mapping(bytesN => V)` value slot is `keccak256(h(key) . slot)` where
// solc stores `h(key)` LEFT-aligned (bytesN stack values are left-aligned;
// Types.h:701-702). A value-type key (uint32) is the right-aligned control.
contract AggregateBytesNMappingKeyHarnessTarget {
    mapping(bytes4 => uint256) private mb4;                        // slot 0
    mapping(uint32 => uint256) private mu32;                       // slot 1 (control)
    mapping(uint256 => mapping(bytes4 => uint256)) private mnest;  // slot 2

    function setKeys() external returns (uint256) {
        mb4[0xaabbccdd] = 111;
        mu32[0xaabbccdd] = 222;
        mnest[7][0xaabbccdd] = 333;
        return 111;
    }

    function readKeys() external view returns (uint256, uint256, uint256) {
        return (mb4[0xaabbccdd], mu32[0xaabbccdd], mnest[7][0xaabbccdd]);
    }
}
