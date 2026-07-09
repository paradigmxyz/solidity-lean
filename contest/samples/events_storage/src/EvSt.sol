// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

contract EvSt {
    event Ping(uint256 indexed a, uint256 b);
    uint256 public slot0;
    uint256 public slot1;

    function run(uint256 x) external returns (uint256) {
        slot0 = x;
        slot1 = x + 1;
        emit Ping(x, x + 2);
        return x + 3;
    }
}
