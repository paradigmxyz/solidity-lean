// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Target {
    function viewGet() external view returns (uint256) {
        return 1;
    }
}

contract UnknownCallOption {
    function run(Target target) external view returns (uint256) {
        return target.viewGet{foo: 1}();
    }
}
