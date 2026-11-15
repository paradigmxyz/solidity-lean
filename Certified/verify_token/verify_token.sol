// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// A minimal token.
contract Token {
    mapping(address => uint256) public balanceOf;
    uint256 public totalSupply;
    address public owner;

    modifier onlyOwner() {
        require(msg.sender == owner, "not owner");
        _;
    }

    /// @custom:ensures owner == msg.sender
    constructor() {
        owner = msg.sender;
    }

    /// @custom:succeeds-if msg.value == 0 && (msg.sender == owner && totalSupply + amount < 2 ** 256 && balanceOf[to] + amount < 2 ** 256)
    /// @custom:ensures balanceOf[to] == old(balanceOf[to]) + amount
    /// @custom:ensures totalSupply == old(totalSupply) + amount
    /// @custom:ensures forall address a :: a != to ==> balanceOf[a] == old(balanceOf[a])
    function mint(address to, uint256 amount) external onlyOwner {
        totalSupply += amount;
        balanceOf[to] += amount;
    }

    /// @custom:succeeds-if msg.value == 0 && (balanceOf[msg.sender] >= amount && (msg.sender == to || balanceOf[to] + amount < 2 ** 256))
    /// @custom:ensures msg.sender != to ==> balanceOf[msg.sender] == old(balanceOf[msg.sender]) - amount
    /// @custom:ensures msg.sender != to ==> balanceOf[to] == old(balanceOf[to]) + amount
    /// @custom:ensures msg.sender == to ==> balanceOf[to] == old(balanceOf[to])
    /// @custom:ensures forall address a :: a != msg.sender && a != to ==> balanceOf[a] == old(balanceOf[a])
    /// @custom:ensures totalSupply == old(totalSupply)
    /// @custom:ensures result == true
    function transfer(address to, uint256 amount) external returns (bool) {
        uint256 bal = balanceOf[msg.sender];
        require(bal >= amount, "insufficient");
        balanceOf[msg.sender] = bal - amount;
        balanceOf[to] += amount;
        return true;
    }

    /// @custom:succeeds-if msg.value == 0 && (balanceOf[msg.sender] >= amount && totalSupply >= amount)
    /// @custom:ensures balanceOf[msg.sender] == old(balanceOf[msg.sender]) - amount
    /// @custom:ensures totalSupply == old(totalSupply) - amount
    /// @custom:ensures forall address a :: a != msg.sender ==> balanceOf[a] == old(balanceOf[a])
    function burn(uint256 amount) external {
        balanceOf[msg.sender] -= amount;
        totalSupply -= amount;
    }
}
