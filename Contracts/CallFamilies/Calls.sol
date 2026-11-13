// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// The external-call families of a constant-product pair, written fresh: a token balance read
// (high-level STATICCALL behind the extcodesize guard), a factory read of the same kind, a token
// transfer through a low-level CALL whose return data must be empty or true, and a callback
// (high-level CALL with no return value).

interface IBalance {
    function balanceOf(address owner) external view returns (uint256);
}

interface IFeeTo {
    function feeTo() external view returns (address);
}

interface ICallback {
    function onFlash(address sender, uint256 amount, bytes calldata data) external;
}

contract Calls {
    bytes4 private constant TRANSFER = bytes4(keccak256(bytes("transfer(address,uint256)")));

    address public factory;
    address public token;
    uint256 public reserve;
    uint256 public kLast;

    function pay(address to, uint256 amount) private {
        (bool ok, bytes memory ret) = token.call(abi.encodeWithSelector(TRANSFER, to, amount));
        require(ok && (ret.length == 0 || abi.decode(ret, (bool))), "TRANSFER_FAILED");
    }

    function sync() external {
        reserve = IBalance(token).balanceOf(address(this));
    }

    function skim(address to) external {
        pay(to, IBalance(token).balanceOf(address(this)) - reserve);
    }

    function feeOn() external returns (bool on) {
        on = IFeeTo(factory).feeTo() != address(0);
        if (on) kLast = 1;
    }

    function flash(address to, uint256 amount, bytes calldata data) external {
        pay(to, amount);
        if (data.length > 0) ICallback(to).onFlash(msg.sender, amount, data);
    }
}
