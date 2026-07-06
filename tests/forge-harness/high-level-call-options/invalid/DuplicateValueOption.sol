// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Target {
    function pay() external payable {}
}

contract DuplicateValueOption {
    function run(Target target) external payable {
        target.pay{value: 1, value: 2}();
    }
}
