contract Events {
    event Transfer(address indexed from, uint256 indexed id, uint256 value);

    /// @custom:succeeds-if msg.value == 0
    function transfer(uint256 id, uint256 value) external {
        emit Transfer(msg.sender, id, value);
    }
}
