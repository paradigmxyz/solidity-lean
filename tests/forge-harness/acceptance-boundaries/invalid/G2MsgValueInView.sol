// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// G2: `msg.value` in a non-payable (view) function — solc TypeError 5887.
contract G2View {
    function f() public view returns (uint) {
        return msg.value;
    }
}
