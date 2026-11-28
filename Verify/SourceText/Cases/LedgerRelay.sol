pragma solidity ^0.8.0;

contract LedgerRelay {
    uint256 public left;
    uint256 public right;
    uint256 public stamp;

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures left == a && right == b && stamp == 17
    function setPair(uint256 a, uint256 b) external {
        left = a;
        right = b;
        stamp = 17;
    }

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures left == old(right) && right == marker && stamp == 3
    function relay(uint256 marker) external {
        left = right;
        right = marker;
        stamp = 3;
    }
}
