// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Callee {
    function boom(uint256 mode) external pure returns (uint256) {
        if (mode == 1) revert("stringerr");
        if (mode == 2) revert();
        return 42;
    }
}
contract TryCatch {
    Callee c;
    constructor() { c = new Callee(); }
    function run(uint256 mode) external returns (uint256) {
        try c.boom(mode) returns (uint256 v) {
            return v;
        } catch Error(string memory) {
            return 100;
        } catch Panic(uint256) {
            return 200;
        } catch (bytes memory) {
            return 300;
        }
    }
}
