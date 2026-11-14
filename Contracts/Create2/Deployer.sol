// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// The inline assembly create2 assignment SolidCore's frontend translates (Stmt.assemblyCreate2):
// a literal value and a bytes32 salt, and every operand a local.
contract Deployer {
    function deploy(bytes32 salt) external returns (address a) {
        bytes memory code = hex"6001600c60003960016000f300";
        assembly {
            a := create2(0, add(code, 32), mload(code), salt)
        }
    }

    function deployWith(uint256 v, uint256 salt, bytes memory code) external payable returns (address a) {
        assembly {
            a := create2(v, add(code, 32), mload(code), salt)
        }
    }
}
