// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract EventFourIndexed {
    event Bad(
        uint256 indexed a,
        uint256 indexed b,
        uint256 indexed c,
        uint256 indexed d
    );
}
