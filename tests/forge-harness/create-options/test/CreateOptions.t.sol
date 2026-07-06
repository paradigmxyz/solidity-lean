// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    CreatedWithOptions,
    CreateOptionsFactory
} from "../src/CreateOptions.sol";

contract CreateOptionsForgeTest {
    CreateOptionsFactory private factory = new CreateOptionsFactory();

    function testMakeWithValueAndSalt() public {
        CreatedWithOptions child =
            factory.make{value: 5}(
                4,
                5,
                bytes32(uint256(0x1234))
            );

        require(child.read() == 9, "child");
    }
}
