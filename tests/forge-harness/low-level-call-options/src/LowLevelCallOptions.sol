// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract LowLevelCallOptionsTarget {
    function echo(bytes calldata payload)
        external
        payable
        returns (bytes memory)
    {
        require(msg.value == 5, "value");
        return payload;
    }

    function read() external view returns (uint256) {
        return 77;
    }
}

contract LowLevelCallOptionsCaller {
    function rawCall(address payable target, bytes memory payload)
        external
        payable
        returns (bool success, bytes memory output)
    {
        return target.call{value: 5, gas: 50000}(payload);
    }

    function rawStatic(address target, bytes memory payload)
        external
        view
        returns (bool success, bytes memory output)
    {
        return target.staticcall{gas: 7000}(payload);
    }
}
