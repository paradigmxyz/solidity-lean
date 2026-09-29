// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {FnPtrReturnedDirectCallTarget} from "../src/FnPtrReturnedDirectCall.sol";

contract FnPtrReturnedDirectCallTest {
    FnPtrReturnedDirectCallTarget target = new FnPtrReturnedDirectCallTarget();

    function testDirectReturn() public view {
        require(target.directReturn() == 8, "direct return");
    }

    function testInitializer() public view {
        require(target.initializer() == 8, "initializer");
    }

    function testEncoded() public view {
        require(keccak256(target.encoded()) == keccak256(abi.encode(uint256(8))), "encoded");
    }

    function testNested() public view {
        require(target.nested() == 9, "nested");
    }
}
