// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Target {
    function pay() external payable returns (uint256) {
        return 1;
    }
}

contract SaltOnHighLevelCall {
    function run(Target target) external {
        target.pay{salt: bytes32(0)}();
    }
}
