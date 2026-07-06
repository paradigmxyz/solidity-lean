// SPDX-License-Identifier: MIT
pragma solidity >0.8.35;

contract BadSolidityPragma {
    function ok() external pure returns (uint256) {
        return 1;
    }
}
