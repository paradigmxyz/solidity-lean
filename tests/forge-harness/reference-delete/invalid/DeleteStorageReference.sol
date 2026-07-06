// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract DeleteStorageReference {
    uint256[] values;

    function bad() external {
        uint256[] storage aliasValue = values;
        delete aliasValue;
    }
}
