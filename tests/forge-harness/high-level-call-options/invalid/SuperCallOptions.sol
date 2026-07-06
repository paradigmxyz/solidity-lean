// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Base {
    function value() public virtual returns (uint256) {
        return 1;
    }
}

contract Bad is Base {
    function value() public override returns (uint256) {
        return super.value{gas: 100}();
    }
}
