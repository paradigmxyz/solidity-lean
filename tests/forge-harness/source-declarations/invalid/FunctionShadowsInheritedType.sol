// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract FunctionShadowTypeBase {
    struct Record {
        uint256 value;
    }
}

contract FunctionShadowsInheritedType is FunctionShadowTypeBase {
    function Record() public pure returns (uint256) {
        return 1;
    }
}
