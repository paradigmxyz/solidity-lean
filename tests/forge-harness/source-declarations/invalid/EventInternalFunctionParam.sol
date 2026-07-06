// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract EventInternalFunctionParam {
    event Bad(function (uint256) internal pure fn);
}
