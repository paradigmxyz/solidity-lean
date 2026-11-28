// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SafeTransfer {
    bytes4 private constant SELECTOR = bytes4(keccak256(bytes("transfer(address,uint256)")));

    function pay(address token, address to, uint256 value) external {
        (bool success, bytes memory data) = token.call(abi.encodeWithSelector(SELECTOR, to, value));
        require(success && (data.length == 0 || abi.decode(data, (bool))), "TRANSFER_FAILED");
    }
}
