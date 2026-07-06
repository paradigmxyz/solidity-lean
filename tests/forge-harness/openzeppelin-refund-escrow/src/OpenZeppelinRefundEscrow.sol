// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Import-free Context slice used by RefundEscrow.
/// @dev Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/utils/Context.sol
abstract contract OpenZeppelinRefundEscrowContext {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

/// @notice Import-free Ownable slice used by RefundEscrow.
/// @dev Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/access/Ownable.sol
abstract contract OpenZeppelinRefundEscrowOwnable is OpenZeppelinRefundEscrowContext {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    constructor() {
        _transferOwnership(_msgSender());
    }

    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    function owner() public view virtual returns (address) {
        return _owner;
    }

    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

/// @notice Import-free Address.sendValue slice used by RefundEscrow.
/// @dev Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/utils/Address.sol
library OpenZeppelinRefundEscrowAddress {
    function sendValue(address payable recipient, uint256 amount) internal {
        require(
            address(this).balance >= amount,
            "Address: insufficient balance"
        );

        (bool success, ) = recipient.call{value: amount}("");
        require(
            success,
            "Address: unable to send value, recipient may have reverted"
        );
    }
}

/// @notice Import-free Escrow slice used by RefundEscrow.
/// @dev Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/utils/escrow/Escrow.sol
contract OpenZeppelinEscrow is OpenZeppelinRefundEscrowOwnable {
    using OpenZeppelinRefundEscrowAddress for address payable;

    event Deposited(address indexed payee, uint256 weiAmount);
    event Withdrawn(address indexed payee, uint256 weiAmount);

    mapping(address => uint256) private _deposits;

    function depositsOf(address payee) public view returns (uint256) {
        return _deposits[payee];
    }

    function deposit(address payee) public payable virtual onlyOwner {
        uint256 amount = msg.value;
        _deposits[payee] += amount;
        emit Deposited(payee, amount);
    }

    function withdraw(address payable payee) public virtual onlyOwner {
        uint256 payment = _deposits[payee];

        _deposits[payee] = 0;

        payee.sendValue(payment);

        emit Withdrawn(payee, payment);
    }
}

/// @notice Import-free ConditionalEscrow slice used by RefundEscrow.
/// @dev Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/utils/escrow/ConditionalEscrow.sol
abstract contract OpenZeppelinConditionalEscrow is OpenZeppelinEscrow {
    function withdrawalAllowed(address payee) public view virtual returns (bool);

    function withdraw(address payable payee) public virtual override {
        require(
            withdrawalAllowed(payee),
            "ConditionalEscrow: payee is not allowed to withdraw"
        );
        super.withdraw(payee);
    }
}

/// @notice Import-free OpenZeppelin Contracts RefundEscrow slice.
/// @dev Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/utils/escrow/RefundEscrow.sol
contract OpenZeppelinRefundEscrow is OpenZeppelinConditionalEscrow {
    using OpenZeppelinRefundEscrowAddress for address payable;

    enum State {
        Active,
        Refunding,
        Closed
    }

    event RefundsClosed();
    event RefundsEnabled();

    State private _state;
    address payable private immutable _beneficiary;

    constructor(address payable beneficiary_) {
        require(
            beneficiary_ != address(0),
            "RefundEscrow: beneficiary is the zero address"
        );
        _beneficiary = beneficiary_;
        _state = State.Active;
    }

    function state() public view virtual returns (State) {
        return _state;
    }

    function beneficiary() public view virtual returns (address payable) {
        return _beneficiary;
    }

    function deposit(address refundee) public payable virtual override {
        require(
            state() == State.Active,
            "RefundEscrow: can only deposit while active"
        );
        super.deposit(refundee);
    }

    function close() public virtual onlyOwner {
        require(
            state() == State.Active,
            "RefundEscrow: can only close while active"
        );
        _state = State.Closed;
        emit RefundsClosed();
    }

    function enableRefunds() public virtual onlyOwner {
        require(
            state() == State.Active,
            "RefundEscrow: can only enable refunds while active"
        );
        _state = State.Refunding;
        emit RefundsEnabled();
    }

    function beneficiaryWithdraw() public virtual {
        require(
            state() == State.Closed,
            "RefundEscrow: beneficiary can only withdraw while closed"
        );
        beneficiary().sendValue(address(this).balance);
    }

    function withdrawalAllowed(address) public view override returns (bool) {
        return state() == State.Refunding;
    }
}
