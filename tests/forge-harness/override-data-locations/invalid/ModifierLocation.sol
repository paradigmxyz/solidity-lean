// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract ModifierLocationBase {
    modifier referenceGuard(uint256[] memory values) virtual {
        require(values.length > 0);
        _;
    }
}

contract ModifierLocation is ModifierLocationBase {
    modifier referenceGuard(uint256[] calldata values) override {
        require(values.length > 0);
        _;
    }
}
