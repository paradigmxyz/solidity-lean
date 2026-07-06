// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad(address target, bytes memory data)
        external
        payable
        returns (bool ok, bytes memory ret)
    {
        return target.call(data: data);
    }
}
