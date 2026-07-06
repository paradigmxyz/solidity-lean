// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ExternalStorageReturn {
    uint256[] values;

    function bad()
        external
        view
        returns (uint256[] storage result)
    {
        return values;
    }
}
