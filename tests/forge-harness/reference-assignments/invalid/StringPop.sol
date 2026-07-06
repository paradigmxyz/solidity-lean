// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StringPop {
    string private text;

    function bad() external {
        text.pop();
    }
}
