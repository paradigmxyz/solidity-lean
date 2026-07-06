// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract HighLevelCallOptionsTarget {
    uint256 private stored;

    constructor(uint256 initial) {
        stored = initial;
    }

    function payQuote(uint256 amount) external payable returns (uint256) {
        require(msg.value == amount, "value");
        return amount + msg.value;
    }

    function viewGet() external view returns (uint256) {
        return stored;
    }
}

contract HighLevelCallOptionsCaller {
    function payKnown(HighLevelCallOptionsTarget target, uint256 amount)
        external
        payable
        returns (uint256)
    {
        return target.payQuote{value: amount, gas: 50000}(amount);
    }

    function readView(HighLevelCallOptionsTarget target)
        external
        view
        returns (uint256)
    {
        return target.viewGet{gas: 4321}();
    }
}
