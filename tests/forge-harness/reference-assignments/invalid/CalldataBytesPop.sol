// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract CalldataBytesPop {
    function bad(bytes calldata data) external pure {
        data.pop();
    }
}
