// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StringPush {
    string private text;

    function bad() external {
        text.push();
    }
}
