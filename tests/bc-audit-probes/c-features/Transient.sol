// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Transient {
    uint256 transient tx1;
    function setGet(uint256 v) external returns (uint256) {
        tx1 = v;
        return tx1;
    }
}
