// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IToken {
    function balanceOf(address owner) external view returns (uint256);
}

contract RetDecode {
    function held(IToken token) external view returns (uint256) {
        return token.balanceOf(address(this));
    }
}
