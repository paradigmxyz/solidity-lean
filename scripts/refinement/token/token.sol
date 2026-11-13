contract Token {
    mapping(address => uint256) balances;
    mapping(address => mapping(address => uint256)) allowances;
    mapping(address => bool) frozen;
    uint256 totalSupply;
    address owner;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    function balanceOf(address who) external view returns (uint256) {
        return balances[who];
    }

    function allowance(address holder, address spender) external view returns (uint256) {
        return allowances[holder][spender];
    }

    function getOwner() external view returns (address) {
        return owner;
    }

    function isFrozen(address who) external view returns (bool) {
        return frozen[who];
    }

    function freeze(address who) external {
        require(msg.sender == owner);
        frozen[who] = true;
    }

    function transfer(address to, uint256 value) external returns (bool) {
        require(!frozen[msg.sender]);
        require(balances[msg.sender] >= value, "balance");
        balances[msg.sender] -= value;
        balances[to] += value;
        emit Transfer(msg.sender, to, value);
        return true;
    }

    function approve(address spender, uint256 value) external returns (bool) {
        allowances[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }

    function transferFrom(address from, address to, uint256 value) external returns (bool) {
        uint256 a = allowances[from][msg.sender];
        if (a < value) {
            revert("allowance");
        } else if (a != type(uint256).max) {
            allowances[from][msg.sender] = a - value;
        }
        require(balances[from] >= value);
        balances[from] -= value;
        balances[to] += value;
        emit Transfer(from, to, value);
        return true;
    }
}
