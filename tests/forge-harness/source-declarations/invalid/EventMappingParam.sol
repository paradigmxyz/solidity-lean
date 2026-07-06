// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract EventMappingParam {
    event Bad(mapping(uint256 => uint256) indexed values);
}
