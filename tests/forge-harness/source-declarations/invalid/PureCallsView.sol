// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PureCallsView {
    function readOnly() public view returns (uint256) {
        return 1;
    }

    function pureCallsView() external pure returns (uint256) {
        return readOnly();
    }
}
