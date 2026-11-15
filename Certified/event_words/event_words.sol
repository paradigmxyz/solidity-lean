// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract EventWords {
    event Swap(address indexed sender, uint256 amount0In, uint256 amount1In, uint256 amount0Out, uint256 amount1Out, address indexed to);

    function swap(uint256 a0, uint256 a1, uint256 b0, uint256 b1, address to) external {
        emit Swap(msg.sender, a0, a1, b0, b1, to);
    }
}
