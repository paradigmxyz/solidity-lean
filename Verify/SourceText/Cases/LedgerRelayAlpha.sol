pragma solidity ^0.8.0;

contract PairBridge {
    uint256 public first;
    uint256 public second;
    uint256 public mark;

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures first == p && second == q && mark == 17
    function store(uint256 p, uint256 q) external {
        first = p;
        second = q;
        mark = 17;
    }

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures first == old(second) && second == m && mark == 3
    function shift(uint256 m) external {
        first = second;
        second = m;
        mark = 3;
    }
}
