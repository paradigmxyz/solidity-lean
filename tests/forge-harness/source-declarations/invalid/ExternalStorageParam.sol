// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ExternalStorageParam {
    function bad(uint256[] storage values)
        external
        view
        returns (uint256)
    {
        return values.length;
    }
}
