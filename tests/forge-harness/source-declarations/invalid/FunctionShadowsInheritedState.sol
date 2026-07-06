// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract FunctionShadowStateBase {
    uint256 internal stored;
}

contract FunctionShadowsInheritedState is FunctionShadowStateBase {
    function stored() public pure returns (uint256) {
        return 1;
    }
}
