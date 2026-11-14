contract Bank {
    mapping(address => uint256) balances;
    uint256 total;

    event Deposit(address indexed who, uint256 amount);

    function credit(address who, uint256 amount) internal returns (uint256) {
        balances[who] += amount;
        total += amount;
        return balances[who];
    }

    /// @custom:succeeds-if msg.value == 0 && (balances[msg.sender] + amount < 2 ** 256 && total + amount < 2 ** 256)
    /// @custom:ensures balances[msg.sender] == old(balances[msg.sender]) + amount
    /// @custom:ensures total == old(total) + amount
    /// @custom:ensures result == balances[msg.sender]
    /// @custom:ensures forall address a :: a != msg.sender ==> balances[a] == old(balances[a])
    function deposit(uint256 amount) external returns (uint256) {
        uint256 b = credit(msg.sender, amount);
        emit Deposit(msg.sender, amount);
        return b;
    }

    /// @custom:succeeds-if msg.value == 0 && (balances[who] + amount < 2 ** 256 && total + amount < 2 ** 256)
    /// @custom:ensures balances[who] == old(balances[who]) + amount
    /// @custom:ensures total == old(total) + amount
    /// @custom:ensures result == balances[who]
    /// @custom:ensures forall address a :: a != who ==> balances[a] == old(balances[a])
    function depositFor(address who, uint256 amount) external returns (uint256) {
        return credit(who, amount);
    }

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures result == balances[who]
    /// @custom:ensures total == old(total)
    /// @custom:ensures forall address a :: balances[a] == old(balances[a])
    function balanceOf(address who) external view returns (uint256) {
        return balances[who];
    }
}
