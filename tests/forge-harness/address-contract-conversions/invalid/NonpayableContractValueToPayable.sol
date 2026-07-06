// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract NonpayableTarget {}

contract NonpayableContractValueToPayable {
    function convert(NonpayableTarget input)
        external
        pure
        returns (address payable)
    {
        return payable(input);
    }
}
